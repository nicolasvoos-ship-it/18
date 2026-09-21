#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""NICO - moteur unique de dossier.

Usage :  python3 nico.py Dossier_Societe_TICKER_AAAA-MM-JJ.json [-o dossier_sortie]

Fait tout ce qui est mecanique, pour que le modele n'ecrive que des faits et des phrases :
  1. calculs financiers (TRI, flux ponderes, P12/P15/P18, capital preserve, horizons,
     regime alternatif, decomposition du TRI, multiple exige, croissance exigee, taille, tranches)
  2. attribution des niveaux de couleur selon le bareme du fichier A (section 13)
  3. controles automatiques (ordre des prix, residus, garde-fous de clause, coherence du verdict)
  4. rendu HTML autonome fond noir (le livrable)
  5. ligne NICO 16 champs + resume de chat

Aucun appel reseau. Les seuils sont ici ET dans le fichier A : ne jamais modifier l'un sans l'autre.
"""
import json, sys, os, re, math, html, copy, hashlib, statistics as stx

TOB, TAX_PV = 0.0035, 0.10
POIDS_DEF = {'baissier': .25, 'central': .50, 'haussier': .25}
VERSION = "V22.4.2"
VERSION_DATE = "21/09/2026"
WARN, CHK = [], []


def warn(m):
    if m not in WARN:
        WARN.append(m)


def chk(lib, etat, note=''):
    CHK.append((lib, etat, note))


# ------------------------------------------------------------------ utilitaires
def V(x):
    """Valeur compacte : scalaire, ou [valeur, provenance, source, note]."""
    if isinstance(x, list) and x and not isinstance(x[0], (list, dict)):
        y = list(x) + ['', '', '']
        return {'v': y[0], 'prov': y[1], 'src': y[2], 'note': y[3]}
    if isinstance(x, dict) and 'v' in x:
        return {'v': x.get('v'), 'prov': x.get('prov', ''), 'src': x.get('source', ''), 'note': x.get('note', '')}
    return {'v': x, 'prov': '', 'src': '', 'note': ''}


def vv(x):
    return V(x)['v']


def G(d, path, default=None):
    cur = d
    for k in path.split('.'):
        if isinstance(cur, dict) and cur.get(k) is not None:
            cur = cur[k]
        else:
            return default
    return cur


def num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool) and not (isinstance(x, float) and math.isnan(x))


def fr(x, d=1, signe=False):
    if not num(x):
        return 'n.d.'
    s = ('%+.*f' % (d, x)) if signe else ('%.*f' % (d, x))
    ent, _, dec = s.partition('.')
    neg = ent.startswith('-') or ent.startswith('+')
    tete, corps = (ent[0], ent[1:]) if neg else ('', ent)
    groupes = []
    while len(corps) > 3:
        groupes.insert(0, corps[-3:])
        corps = corps[:-3]
    groupes.insert(0, corps)
    out = tete + '\u202f'.join(groupes)
    return out + (',' + dec if dec else '')


def fprix(p):
    return 'n.d.' if not num(p) else fr(p, 0 if abs(p) >= 100 else 1 if abs(p) >= 10 else 2)


# ------------------------------------------------------------------ niveaux
def cut(x, bornes, niveaux):
    if not num(x):
        return 'gris'
    for b, n in zip(bornes, niveaux):
        if x < b:
            return n
    return niveaux[-1]


L_PCT = lambda x: cut(x, [25, 40, 55, 70, 90], [1, 2, 3, 4, 5, 6])
L_RDT = lambda x: cut(x, [0, 8, 12, 15, 18], [1, 2, 3, 4, 5, 6])
L_CAP = lambda x: cut(x, [50, 70, 80, 90, 100], [1, 2, 3, 4, 5, 6])
L_SECT = lambda x: cut(x, [-5, 0, 3, 6, 10], [1, 2, 3, 4, 5, 6])
L_SPREAD = lambda x: cut(x, [0, 2, 4], [2, 3, 4, 5])
L_ECART = lambda x: cut(x, [0, 3, 6], [5, 4, 3, 2])
L_CENT = lambda p: 'gris' if not num(p) else (6 if p <= 25 else 5 if p <= 50 else 4 if p <= 75 else 3 if p <= 90 else 2 if p <= 97 else 1)
L_PART = lambda p: 'gris' if not num(p) else (2 if p > 50 else 3 if p > 40 else 4 if p > 25 else 5)


def L_D(d, gain_etaye=False):
    """Echelle d du stress -20 % et des canaux de regime (pire borne)."""
    if not num(d):
        return 'gris'
    if d <= -40: return 1
    if d <= -20: return 2
    if d <= -5:  return 3
    if d < -1:   return 4
    if d <= 1:   return 5
    return 6 if gain_etaye else 5


FAM = {
    'ia': {'MENAC\u00c9, MOTEUR': 1, 'MOTEUR PRINCIPAL COMPROMIS': 1, 'MESUR\u00c9': 6, 'PLAUSIBLE': 5,
           'NEUTRE \u00c9TAY\u00c9': 4, 'MENAC\u00c9': 2, 'IND\u00c9TERMIN\u00c9': 'gris'},
    'capex': {'DIRECT MAT\u00c9RIEL': 2, 'IND\u00c9TERMIN\u00c9': 'gris', 'INDIRECT': 4, 'DIRECT': 3, 'FAIBLE': 5},
    'prix': {'INT\u00c9GRAL': 6, 'EXCEPTIONNEL': 6, 'FORT': 5, 'INDEX\u00c9': 4, 'LIMIT\u00c9': 3,
             'SUBI': 2, 'N\u00c9GATIF': 2, 'IND\u00c9TERMIN\u00c9': 'gris', 'PLAUSIBLE NON D\u00c9MONTR\u00c9': 'gris'},
    'invest': {'SOUS LE CO\u00dbT': 2, 'EN AM\u00c9LIORATION': 5, 'STABLES': 4, 'EN BAISSE': 3, 'INCONNUS': 'gris'},
    'protection': {'MARCH\u00c9 MA\u00ceTRIS\u00c9': 5, 'EXTENSION': 4, 'NOUVEAU TERRAIN': 3, 'NON DOCUMENT\u00c9': 'gris'},
    'resultats': {'R\u00c9VISION DURABLE': 6, 'ALERTE MOD\u00c9LIS\u00c9E': 3, 'D\u00c9T\u00c9RIORATION': 2,
                  'CONFIRMATION': 5, 'INFLEXION': 4, 'VETO': 1, 'IND\u00c9TERMIN\u00c9': 'gris'},
    'inities': {'VENTES NON CORROBOR\u00c9ES': 3, 'ACHATS SIGNIFICATIFS': 6, 'VENTES CORROBOR\u00c9ES': 2,
                'ACHATS LIMIT\u00c9S': 5, 'NEUTRE V\u00c9RIFI\u00c9': 4, 'INDISPONIBLE': 'gris'},
    'actionnariat': {'FONDATEUR ALIGN\u00c9': 6, 'FAMILLE': 6, 'CONTR\u00d4LE SANS ALIGNEMENT': 3,
                     'INITI\u00c9S SIGNIFICATIFS': 5, 'CAPITAL DISPERS\u00c9': 4, 'EXTRACTION': 2, 'NON DOCUMENT\u00c9': 'gris'},
    'kpi': {'CROISSANCE SANS CO\u00dbT': 3, 'ALIGN\u00c9 PAR ACTION': 6, 'NON PUBLI\u00c9': 'gris',
            'D\u00c9SALIGN\u00c9': 2, 'ALIGN\u00c9': 5, 'MIXTE': 4},
    'achat': {'WATCHLIST \u2014 CONFIRMATION': 3, 'WATCHLIST \u2014 GUIDANCE': 3, 'ACHAT COMPL\u00c9MENTAIRE': 5,
              'HORS P\u00c9RIM\u00c8TRE': 'doc', 'WATCHLIST PROCHE': 4, 'WATCHLIST LOIN': 3, 'HORS S\u00c9LECTION': 2,
              '\u00c0 DOCUMENTER': 'doc', 'RENFORCEMENT': 5, 'CONFIRMATION': 3, 'GUIDANCE': 3, 'REJET': 1, 'ACHAT': 6},
    'suivi': {'SOUS SURVEILLANCE': 4, 'SP\u00c9CULATIVE': 3, 'CONSERVER': 5, 'RETIRER': 2},
    'fiab': {'A': 6, 'B': 5, 'C': 3, 'D': 1},
    'momentum': {'FAVORABLE': 5, 'D\u00c9FAVORABLE': 3, 'MIXTE': 4, 'IND\u00c9TERMIN\u00c9': 'gris'},
    'mult_exige': {'COMPATIBLE': 5, 'EXIGEANT': 3, 'NON \u00c9TAY\u00c9': 2},
    'resilience': {'ROBUSTE': 5, 'PARI DE R\u00c9GIME': 3, 'SENSIBLE': 4, 'PEU SENSIBLE': 4, 'NON \u00c9VALU\u00c9': 'gris'},
}


def L_LAB(fam, lab):
    if not lab:
        return 'gris'
    u = str(lab).upper()
    for k in sorted(FAM[fam], key=len, reverse=True):
        if k in u:
            return FAM[fam][k]
    return 'gris'


# ------------------------------------------------------------------ qualite
PIL = [('modele', 'Mod\u00e8le, moat, durabilit\u00e9', 20), ('visibilite', 'Visibilit\u00e9 des flux', 15),
       ('capital', 'Rendement du capital', 20), ('cash', 'Cash et sinc\u00e9rit\u00e9', 15),
       ('bilan', 'Bilan et financement', 15), ('direction', 'Direction et allocation', 15)]


TX_BASE, TX_MIN, TX_MAX = 15.0, 12.0, 21.0
DROITS = {'SOLIDES': 0.0, 'STANDARD': 0.0, 'FRAGILES': 2.0,
          'TRES FRAGILES': 3.0, 'TR\u00c8S FRAGILES': 3.0,
          'NON DOCUMENTE': 1.0, 'NON DOCUMENT\u00c9': 1.0}


def L_RDT_TX(x, tx):
    """Couleur du rendement RELATIVE au taux exige de la ligne (grille 4 bandes)."""
    if not (num(x) and num(tx)):
        return 'gris'
    return 5 if x >= tx else 4 if x >= tx - 5 else 3 if x >= tx - 10 else 2


def calc_taux_exige(D, R):
    """Taux exige = 15 % + modificateurs ecrits, borne 12-21 %.
    Ne facture QUE le risque non modelisable dans les flux (R3)."""
    meta = D.get('meta') or {}
    q = R.get('q') or {}
    rb = R.get('rentab') or {}
    tx_in = D.get('taux_exige') or {}
    mods = []

    Q, vis = q.get('Q'), q.get('vis')
    iqr, ab, nn = rb.get('iqr'), rb.get('au_dessus'), rb.get('n')
    if (num(Q) and Q >= 85 and num(vis) and vis >= 70 and num(iqr) and iqr <= 5
            and num(ab) and num(nn) and nn >= 5 and ab >= 5):
        mods.append(('qualit\u00e9 prouv\u00e9e (Q\u226585, visibilit\u00e9\u226570 %, IQR ROIC\u22645 pts, 5 ans ROIC>WACC)', -2.0))

    vn = ((q.get('pil') or {}).get('visibilite') or {}).get('notes') or []
    if vn and num(vn[0]) and vn[0] >= 1:
        mods.append(('base contract\u00e9e ou r\u00e9currente prouv\u00e9e (Visibilit\u00e9 1 = 1)', -1.0))

    capm = vv(meta.get('capitalisation_meur'))
    if num(capm):
        if capm < 150:
            mods.append(('capitalisation <150 M\u20ac', 2.0))
        elif capm < 500:
            mods.append(('capitalisation <500 M\u20ac', 1.0))
    else:
        warn('Capitalisation absente de meta : prime de taille non appliqu\u00e9e au taux exig\u00e9.')

    dr = tx_in.get('droits_actionnaire')
    lab = (dr[0] if isinstance(dr, list) and dr else dr) or ''
    key = str(lab).strip().upper()
    if key in DROITS:
        if DROITS[key]:
            mods.append(('droits de l\'actionnaire : %s' % key.lower(), DROITS[key]))
    elif key:
        mods.append(('droits de l\'actionnaire : libell\u00e9 invalide, trait\u00e9 comme NON DOCUMENT\u00c9', 1.0))
        warn('Libell\u00e9 de droits de l\'actionnaire non reconnu (%s) : trait\u00e9 comme NON DOCUMENT\u00c9, +1 pt.' % key)
        chk('Droits de l\'actionnaire document\u00e9s', '\u00e9chec', 'libell\u00e9 invalide : %s' % key)
    else:
        mods.append(('droits de l\'actionnaire non renseign\u00e9s (trait\u00e9s comme NON DOCUMENT\u00c9)', 1.0))
        warn('Droits de l\'actionnaire non renseign\u00e9s : prime de +1 pt appliqu\u00e9e d\'office, champ \u00e0 documenter.')
        chk('Droits de l\'actionnaire document\u00e9s', '\u00e9chec', 'champ absent \u2014 oublier le champ ne peut pas am\u00e9liorer le prix')

    fiab = (meta.get('fiabilite') or 'B').upper()[:1]
    if fiab == 'C':
        mods.append(('fiabilit\u00e9 C (incertitude mat\u00e9rielle born\u00e9e)', 1.0))

    # Cyclicite et levier : PAS de prime de taux (R3) \u2014 deja chiffres dans le scenario
    # baissier, dans les frais financiers (canal 1) et dans le pilier Bilan.

    aj, mot = tx_in.get('ajustement'), tx_in.get('motif')
    if num(aj) and aj:
        if mot:
            a = max(-2.0, min(2.0, float(aj)))
            mods.append(('ajustement motiv\u00e9 : %s' % mot, a))
        else:
            warn('Ajustement manuel du taux exig\u00e9 ignor\u00e9 : motif absent.')

    brut = TX_BASE + sum(m[1] for m in mods)
    tx = max(TX_MIN, min(TX_MAX, round(brut * 2) / 2))
    R['tx'] = tx
    R['tx_mods'] = mods
    R['tx_brut'] = brut
    R['tx_borne'] = abs(brut - tx) > 1e-9
    if brut > TX_MAX + 1e-9:
        warn('Taux exig\u00e9 brut %.1f %% > %.0f %% : le risque d\u00e9passe ce qu\'un prix peut compenser. '
             'Aucun ACHAT sans justification \u00e9crite \u2014 orientation HORS S\u00c9LECTION.' % (brut, TX_MAX))
        chk('Taux exig\u00e9 dans la plage 12\u201321 %%', '\u00e9chec', 'brut %.1f %%' % brut)
    elif brut < TX_MIN - 1e-9:
        warn('Taux exig\u00e9 brut %.1f %% < %.0f %% : plancher appliqu\u00e9.' % (brut, TX_MIN))
    chk('Taux exig\u00e9 calcul\u00e9 par le moteur', 'valid\u00e9',
        '%.1f %% (base 15 %%, %d modificateur(s)%s)' % (tx, len(mods), ', born\u00e9' if R['tx_borne'] else ''))
    return tx


def calc_qualite(q, wacc_absent):
    ctr = q.get('controles') or {}
    num_, den = 0.0, 0.0
    pil = {}
    for k, lab, w in PIL:
        cs = (ctr.get(k) or [])[:3]
        notes, textes = [], []
        for i in range(3):
            c = cs[i] if i < len(cs) else None
            if isinstance(c, list):
                notes.append(c[0]); textes.append(c[1] if len(c) > 1 else '')
            else:
                notes.append(c); textes.append('')
        if k == 'capital' and wacc_absent and num(notes[0]) and notes[0] > 0.5:
            notes[0] = 0.5
            warn('WACC absent : contr\u00f4le Capital 1 plafonn\u00e9 \u00e0 0,5 par le moteur.')
        obs = [n for n in notes if num(n)]
        for n in obs:
            num_ += w / 3 * n
            den += w / 3
        pil[k] = {'lab': lab, 'poids': w, 'obs': len(obs), 'notes': notes, 'textes': textes,
                  'pct': (100 * sum(obs) / len(obs)) if obs else None}
    Q = 100 * num_ / den if den else None
    cov = den
    partiel = [k for k, p in pil.items() if p['obs'] < 3]
    provisoire = (cov < 80) or any(p['obs'] < 2 for p in pil.values())
    m = pil['modele']['notes']
    porte = (num(Q) and Q >= 70 and cov >= 80 and not provisoire and not q.get('blocage')
             and num(m[1]) and m[1] >= 0.5 and num(m[2]) and m[2] >= 0.5
             and all((p['pct'] is not None and p['pct'] >= 50) for k, p in pil.items() if k != 'visibilite')
             and pil['visibilite']['pct'] is not None and pil['visibilite']['pct'] >= 30)
    vis = pil['visibilite']['pct']
    return {'Q': Q, 'cov': cov, 'pil': pil, 'partiel': partiel, 'provisoire': provisoire,
            'porte': bool(porte), 'vis': vis, 'niveau': L_PCT(Q)}


def roic_badge(serie, wacc):
    vals = [s[1] for s in (serie or []) if isinstance(s, (list, tuple)) and num(s[1])]
    out = {'n': len(vals), 'med': None, 'min': None, 'last': None, 'au_dessus': None, 'iqr': None,
           'vals': vals, 'annees': [s[0] for s in (serie or []) if isinstance(s, (list, tuple)) and num(s[1])],
           'wacc': wacc}
    n = len(vals)
    if n == 0:
        return dict(out, lab='NON DOCUMENT\u00c9E', lvl='gris')
    out['med'], out['min'], out['last'] = stx.median(vals), min(vals), vals[-1]
    if n >= 4:
        qs = stx.quantiles(vals, n=4, method='inclusive')
        out['iqr'] = qs[2] - qs[0]
    if n < 3:
        return dict(out, lab='HISTORIQUE INSUFFISANT', lvl='gris')
    if not num(wacc):
        return dict(out, lab='CO\u00dbT DU CAPITAL NON \u00c9VALU\u00c9', lvl='gris')
    ab = sum(1 for v in vals if v > wacc)
    out['au_dessus'] = ab
    iqr = out['iqr'] if out['iqr'] is not None else 0
    if n >= 5 and out['med'] <= 0:
        lab, l = 'DESTRUCTION PERSISTANTE', 1
    elif out['med'] <= wacc:
        lab, l = 'SOUS LE CO\u00dbT DU CAPITAL', 2
    elif ab <= n / 2 or out['last'] <= wacc:
        lab, l = 'FRAGILE', 3
    elif ab < n or iqr > 5:
        lab, l = 'IRR\u00c9GULI\u00c8RE', 4
    elif n < 5:
        lab, l = 'HISTORIQUE COURT', 4
    elif out['min'] >= wacc + 3 and out['med'] >= wacc + 8:
        lab, l = 'RENTABILIT\u00c9 DURABLE EXCEPTIONNELLE', 6
    else:
        lab, l = 'RENTABLE ET STABLE', 5
    if n < 5 and isinstance(l, int) and l > 4:
        lab, l = 'HISTORIQUE COURT', 4
    return dict(out, lab=lab, lvl=l)


def barC(x):
    if not num(x):
        return None
    return 100 if x >= 15 else 80 if x >= 10 else 60 if x >= 6 else 35 if x >= 3 else 10 if x >= 0 else 0


# ------------------------------------------------------------------ moteur financier
def bpa_at(sc, base, t, gt):
    b = [base if num(base) else sc['bpa'][0]] + list(sc['bpa'])
    if t <= 4:
        i = int(math.floor(t)); f = t - i
        if f == 0:
            return b[i]
        a, c = b[i], b[i + 1]
        return a * (c / a) ** f if (a > 0 and c > 0) else a + (c - a) * f
    return b[4] * (1 + gt / 100.0) ** (t - 4)


def dps_at(sc, k, gt):
    d = sc.get('dps') or [0, 0, 0, 0]
    return d[k - 1] if k <= 4 else d[3] * (1 + gt / 100.0) ** (k - 4)


def fx_at(sc, x0, t):
    f = sc.get('fx')
    if not f:
        return x0
    return f[min(max(int(math.ceil(t)), 1), 4) - 1]


def flux(P, sc, ctx, h=4.0, mult=None, divs=True):
    x0 = ctx['x0']; B = P * x0
    I0 = B * (1 + TOB + ctx['fa'])
    cf = {0.0: -I0}
    if divs:
        for k in range(1, int(math.floor(h)) + 1):
            cf[float(k)] = cf.get(float(k), 0.0) + dps_at(sc, k, ctx['gt']) * fx_at(sc, x0, k) * ctx['net_div']
    m = sc['multiple'] if mult is None else mult
    S = max(0.0, bpa_at(sc, ctx['base'], h, ctx['gt']) * m * fx_at(sc, x0, h))
    vente = S - TAX_PV * max(S - B, 0.0) - S * (TOB + ctx['fv'])
    cf[float(h)] = cf.get(float(h), 0.0) + vente
    return sorted(cf.items()), I0


def flux_pond(P, scs, ctx, h=4.0, mult_central=None):
    tot = {}
    for nom in ('baissier', 'central', 'haussier'):
        sc = scs[nom]
        w = sc.get('poids', POIDS_DEF[nom])
        cfs, _ = flux(P, sc, ctx, h, mult_central if nom == 'central' else None)
        for t, c in cfs:
            tot[t] = tot.get(t, 0.0) + w * c
    return sorted(tot.items())


def npv(r, cfs):
    return sum(c / (1 + r) ** t for t, c in cfs)


def tri(cfs):
    pos = sum(c for t, c in cfs if t > 0 and c > 0)
    if pos <= 0:
        return -100.0
    lo, hi = -0.95, 5.0
    flo, fhi = npv(lo, cfs), npv(hi, cfs)
    if flo * fhi > 0:
        return None
    for _ in range(160):
        mid = (lo + hi) / 2
        if (npv(mid, cfs) > 0) == (flo > 0):
            lo = mid
        else:
            hi = mid
    return 100 * (lo + hi) / 2


def prix_pour(r, fabrique, pmax):
    f = lambda P: npv(r, fabrique(P))
    lo, hi = 1e-6, max(pmax, 1.0)
    if f(lo) <= 0:
        return None
    n = 0
    while f(hi) > 0 and n < 40:
        hi *= 2; n += 1
    if f(hi) > 0:
        return None
    for _ in range(140):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def cap_preserve(P, sc, ctx):
    cfs, I0 = flux(P, sc, ctx)
    return 100 * sum(c for t, c in cfs if t > 0) / I0


# ------------------------------------------------------------------ V22.4.2 : normalisation des entrees
# Tout champ lu comme nombre (ou libelle) par le calcul accepte indifferemment une valeur nue ou le format
# compact [valeur, provenance, source, note]. Les champs deja lus via vv() gardent leur provenance a l'affichage.
CHAMPS_NUM = [
    'meta.fx_eur', 'meta.liquidite_max_pct',
    'taux_exige.ajustement',
    'croissance.g_centrale', 'croissance.g_organique_hist',
    'valo.frais_achat_pct', 'valo.frais_vente_pct', 'valo.retenue_etrangere', 'valo.precompte',
    'valo.croissance_terminale', 'valo.multiple_actuel', 'valo.mediane_5ans', 'valo.pairs',
    'valo.bas_fourchette_5ans', 'valo.ancrage_terminal.plafond',
    'momentum.perf6m_rel', 'momentum.vs_mm200',
    'risques.stress.d_bas', 'risques.stress.d_haut',
    'secteur.s_bas', 'secteur.s_haut',
    'resultats.reperes.ca_n1', 'resultats.reperes.ca_attentes',
    'resultats.reperes.bpa_n1', 'resultats.reperes.bpa_attentes',
]
CHAMPS_NUM_VV = ['meta.cours', 'meta.capitalisation_meur', 'valo.base_normalisee', 'valo.base_publiee',
                 'rentabilite.wacc']  # lus via vv() : seule la valeur interne est controlee
CHAMPS_TXT = ['meta.fiabilite', 'valo.clause', 'taux_exige.motif']


def _en_nombre(x):
    """Nombre, None, ou chaine numerique ('0,30', '15 %') convertie ; sinon leve ValueError."""
    if x is None or num(x):
        return x
    if isinstance(x, bool):
        raise ValueError(x)
    if isinstance(x, str):
        t = x.strip().replace('\u00a0', '').replace(' ', '').replace('%', '').replace(',', '.')
        if t in ('', 'n.d.', 'nd', 'null', 'None'):
            return None
        return float(t)
    raise ValueError(x)


def _chemin(D, path):
    *tete, cle = path.split('.')
    cur = D
    for k in tete:
        if not isinstance(cur, dict) or not isinstance(cur.get(k), dict):
            return None, None
        cur = cur[k]
    return (cur, cle) if isinstance(cur, dict) and cle in cur else (None, None)


def normaliser_entrees(D):
    """Deballe les formats compacts la ou le calcul attend un scalaire ; ne plante jamais."""
    prov = D.setdefault('_prov_deballee', {})
    notes = []

    def fixe(path, garder_liste=False):
        parent, cle = _chemin(D, path)
        if parent is None:
            return
        brut = parent[cle]
        val = brut
        if isinstance(brut, dict) and 'v' in brut:
            val = brut.get('v')
        elif isinstance(brut, list) and brut and not isinstance(brut[0], (list, dict)):
            val = brut[0]
        try:
            n = _en_nombre(val)
        except (ValueError, TypeError):
            notes.append('%s illisible (%r) \u2014 trait\u00e9 comme n.d.' % (path, val))
            n = None
        if garder_liste and isinstance(brut, list):
            brut = list(brut); brut[0] = n; parent[cle] = brut
        elif garder_liste and isinstance(brut, dict):
            brut = dict(brut); brut['v'] = n; parent[cle] = brut
        else:
            if val is not brut:
                prov[path] = V(brut)
            parent[cle] = n

    for p in CHAMPS_NUM:
        fixe(p)
    for p in CHAMPS_NUM_VV:
        fixe(p, garder_liste=True)
    for p in CHAMPS_TXT:
        parent, cle = _chemin(D, p)
        if parent is not None and isinstance(parent[cle], (list, dict)):
            prov[p] = V(parent[cle]); parent[cle] = str(V(parent[cle])['v'] or '')

    scs = G(D, 'valo.scenarios') or {}
    for nom, sc in (scs.items() if isinstance(scs, dict) else []):
        if not isinstance(sc, dict):
            continue
        for k in ('multiple', 'poids'):
            if k in sc:
                x = sc[k]
                if isinstance(x, list) and x and not isinstance(x[0], (list, dict)):
                    x = x[0]
                try:
                    sc[k] = _en_nombre(x)
                except (ValueError, TypeError):
                    notes.append('sc\u00e9nario %s.%s illisible \u2014 n.d.' % (nom, k)); sc[k] = None
        if sc.get('poids') is None and nom in POIDS_DEF:
            sc['poids'] = POIDS_DEF[nom]
        for k in ('bpa', 'dps'):
            if isinstance(sc.get(k), list):
                propre = []
                for x in sc[k]:
                    if isinstance(x, list) and x and not isinstance(x[0], (list, dict)):
                        x = x[0]
                    try:
                        propre.append(_en_nombre(x))
                    except (ValueError, TypeError):
                        notes.append('sc\u00e9nario %s.%s illisible \u2014 n.d.' % (nom, k)); propre.append(None)
                sc[k] = propre
    return notes


def calculer(D):
    WARN.clear()
    CHK.clear()
    for n_ in normaliser_entrees(D):
        warn(n_)
    R = {'calc': False}
    meta = D.get('meta') or {}
    valo = D.get('valo') or {}
    cours = vv(meta.get('cours')); x0 = meta.get('fx_eur', 1.0) or 1.0
    rent = D.get('rentabilite') or {}
    R['rentab'] = roic_badge(rent.get('roic'), vv(rent.get('wacc')))
    R['q'] = calc_qualite(D.get('qualite') or {}, not num(vv(rent.get('wacc'))))
    calc_taux_exige(D, R)

    scs = valo.get('scenarios') or {}
    base = vv(valo.get('base_normalisee'))
    gc = G(D, 'croissance.g_centrale')
    if not num(gc) and scs.get('central') and num(base) and base > 0 and scs['central']['bpa'][3] > 0:
        gc = 100 * ((scs['central']['bpa'][3] / base) ** 0.25 - 1)
    go = G(D, 'croissance.g_organique_hist')
    R['gc'], R['go'] = gc, go
    bo, bg = barC(go), barC(gc)
    R['C'] = None if (bo is None or bg is None) else 0.5 * bo + 0.5 * bg

    def _sc_ok(sc):  # V22.4.1 : un scenario incomplet vaut arret precoce, jamais un plantage
        return (isinstance(sc, dict) and isinstance(sc.get('bpa'), list) and len(sc['bpa']) == 4
                and all(num(x) for x in sc['bpa']) and num(sc.get('multiple')))
    if not (num(cours) and all(_sc_ok(scs.get(k)) for k in ('baissier', 'central', 'haussier'))):
        chk('Calculs financiers', 'n.a.', 'sc\u00e9narios ou cours absents \u2014 arr\u00eat pr\u00e9coce')
        return R

    wsum = sum(scs[k].get('poids', POIDS_DEF[k]) for k in ('baissier', 'central', 'haussier'))
    if abs(wsum - 1) > 1e-6:
        warn('Somme des poids de sc\u00e9narios = %.2f (attendu 1,00).' % wsum)
    gt = valo.get('croissance_terminale')
    der = None
    c4, c3 = scs['central']['bpa'][3], scs['central']['bpa'][2]
    if c3 > 0:
        der = 100 * (c4 / c3 - 1)
    cands = [x for x in (gt, gc, der) if num(x)]
    gt = min(cands) if cands else 0.0
    ctx = {'x0': x0, 'base': base, 'gt': gt,
           'fa': (valo.get('frais_achat_pct') or 0) / 100.0,
           'fv': (valo.get('frais_vente_pct') or 0) / 100.0,
           'net_div': (1 - (valo.get('retenue_etrangere') or 0)) * (1 - (valo.get('precompte', 0.30) or 0))}
    R['ctx'] = ctx
    C, Bs = scs['central'], scs['baissier']

    cf_c, I0 = flux(cours, C, ctx)
    R['tri_central'] = tri(cf_c)
    R['tri_pondere'] = tri(flux_pond(cours, scs, ctx))
    dispo = [t for t in (R['tri_central'], R['tri_pondere']) if num(t)]
    R['retenu'] = min(dispo) if dispo else None
    R['niv_retenu'] = L_RDT_TX(R['retenu'], R.get('tx'))

    mact = valo.get('multiple_actuel')
    R['tri_mult_constant'] = tri(flux(cours, C, ctx, 4, mact)[0]) if num(mact) else None
    A_ = tri(flux(cours, C, ctx, 4, mact, divs=False)[0]) if num(mact) else None
    B_ = tri(flux(cours, C, ctx, 4, mact)[0]) if num(mact) else None
    Cc = R['tri_central']
    R['decomp'] = {'A': A_, 'B': B_, 'C': Cc,
                   'div': (B_ - A_) if (num(A_) and num(B_)) else None,
                   'mult': (Cc - B_) if (num(B_) and num(Cc)) else None}
    R['part_mult'] = (max(0.0, Cc - B_) / Cc * 100) if (num(B_) and num(Cc) and Cc > 0) else None
    R['niv_part'] = L_PART(R['part_mult'])

    pmax = cours * 20

    def _prix(r):
        pc = prix_pour(r, lambda P: flux(P, C, ctx)[0], pmax)
        pp = prix_pour(r, lambda P: flux_pond(P, scs, ctx), pmax)
        c_ = [p for p in (pc, pp) if num(p)]
        return min(c_) if c_ else None

    for r, nom in ((0.12, 'P12'), (0.15, 'P15'), (0.18, 'P18')):
        R[nom] = _prix(r)
    tx = R.get('tx') or 15.0
    R['tx_bandes'] = (tx, max(2.0, tx - 5), max(2.0, tx - 10))
    R['PA'] = _prix(tx / 100.0)
    R['PJ'] = _prix(R['tx_bandes'][1] / 100.0)
    R['PO'] = _prix(R['tx_bandes'][2] / 100.0)
    R['PR'] = _prix(min(0.30, (tx + 3) / 100.0))
    R['PS'] = _prix(min(0.30, (tx + 6) / 100.0))
    R['tx_action'] = (tx, min(30.0, tx + 3), min(30.0, tx + 6))
    R['PA_sans_revalo'] = prix_pour(tx / 100.0, lambda P: flux(P, C, ctx, 4, mact)[0], pmax) if num(mact) else None
    R['P15_sans_revalo'] = prix_pour(0.15, lambda P: flux(P, C, ctx, 4, mact)[0], pmax) if num(mact) else None
    if all(num(R[k]) for k in ('PA', 'PJ', 'PO')):
        okb = R['PA'] <= R['PJ'] <= R['PO'] + 1e-9
        chk('Ordre des bandes de prix (achat \u2264 \u22125 pts \u2264 \u221210 pts)', 'valid\u00e9' if okb else '\u00e9chec')
        if not okb:
            warn('Ordre des bandes de prix incoh\u00e9rent : v\u00e9rifier les flux.')
    if all(num(R[k]) for k in ('PA', 'PR', 'PS')):
        oka = R['PS'] <= R['PR'] <= R['PA'] + 1e-9
        chk('Ordre des prix actionnables (+6 pts \u2264 +3 pts \u2264 objectif)',
            'valid\u00e9' if oka else '\u00e9chec')
        if not oka:
            warn('Ordre des prix actionnables incoh\u00e9rent : v\u00e9rifier les flux.')
    if all(num(R[k]) for k in ('P12', 'P15', 'P18')):
        ok = R['P18'] <= R['P15'] <= R['P12'] + 1e-9
        chk('Ordre P18 \u2264 P15 \u2264 P12', 'valid\u00e9' if ok else '\u00e9chec')
        if not ok:
            warn('Ordre des prix incoh\u00e9rent : v\u00e9rifier les flux.')
        res = max(min(abs(npv(r, flux(R[n], C, ctx)[0])), abs(npv(r, flux_pond(R[n], scs, ctx))))
                  for r, n in ((0.12, 'P12'), (0.15, 'P15'), (0.18, 'P18')))
        lim = 'central' if abs(npv(0.15, flux(R['P15'], C, ctx)[0])) < 1e-4 else 'flux pond\u00e9r\u00e9s'
        chk('R\u00e9sidus de VAN aux prix r\u00e9solus', 'valid\u00e9' if res < 1e-4 else '\u00e9chec',
            'max %.2e \u00b7 prix limit\u00e9 par les %s' % (res, lim))

    R['cap_cours'] = cap_preserve(cours, Bs, ctx)
    R['cap_P15'] = cap_preserve(R['P15'], Bs, ctx) if num(R['P15']) else None
    R['cap_PA'] = cap_preserve(R['PA'], Bs, ctx) if num(R['PA']) else None
    R['niv_cap'] = L_CAP(R['cap_cours'])
    R['ecart_P15'] = (cours - R['P15']) / cours * 100 if num(R['P15']) else None
    R['ecart_PA'] = (cours - R['PA']) / cours * 100 if num(R['PA']) else None

    R['horizons'] = {}
    for h in (2.5, 4.0, 6.5):
        R['horizons'][h] = {'avec': tri(flux(cours, C, ctx, h)[0]),
                            'sans': tri(flux(cours, C, ctx, h, mact)[0]) if num(mact) else None}
    R['tri_bear_25'] = tri(flux(cours, Bs, ctx, 2.5)[0])

    # --- tolerance a l'erreur : de combien le central peut se tromper au prix d'achat
    R['tolerance'] = None
    plancher = max(0.0, (R.get('tx') or 15.0) - 5.0)
    if num(R.get('PA')) and R['PA'] > 0:
        def tri_k(k):
            s2 = dict(C); s2['bpa'] = [x * k for x in C['bpa']]
            return tri(flux(R['PA'], s2, ctx)[0])
        lo, hi = 0.20, 1.0
        if num(tri_k(lo)) and tri_k(lo) < plancher:
            for _ in range(60):
                mid = (lo + hi) / 2
                t_ = tri_k(mid)
                if not num(t_):
                    break
                if t_ < plancher:
                    lo = mid
                else:
                    hi = mid
            R['tolerance'] = (1 - (lo + hi) / 2) * 100
    R['tolerance_plancher'] = plancher
    R['ecart_hist'] = (gc - go) if (num(gc) and num(go)) else None

    # multiple exige par le cours
    txf = (R.get('tx') or 15.0) / 100.0
    f = lambda m: npv(txf, flux(cours, C, ctx, 4, m)[0])
    if f(0.0) >= 0:
        R['mult_exige'] = 0.0
    else:
        lo, hi = 0.0, 5.0
        n = 0
        while f(hi) < 0 and n < 40:
            hi *= 2; n += 1
        R['mult_exige'] = None if f(hi) < 0 else (lambda: None)()
        if f(hi) >= 0:
            for _ in range(120):
                mid = (lo + hi) / 2
                if f(mid) < 0:
                    lo = mid
                else:
                    hi = mid
            R['mult_exige'] = (lo + hi) / 2
    refs = [r_ for r_ in (mact, valo.get('mediane_5ans'), valo.get('pairs')) if num(r_)]
    me = R['mult_exige']
    if not num(me):
        R['mult_exige_lab'] = 'NON \u00c9TAY\u00c9'
    elif num(C.get('multiple')) and me <= C['multiple'] + 1e-9:
        R['mult_exige_lab'] = 'COMPATIBLE'
    elif refs and me <= max(refs):
        R['mult_exige_lab'] = 'EXIGEANT'
    else:
        R['mult_exige_lab'] = 'NON \u00c9TAY\u00c9'

    # croissance exigee (inversion mecanique, seuil indicatif)
    R['g_exigee'] = None
    if num(base) and base > 0:
        def tri_g(g):
            s2 = dict(C); s2['bpa'] = [base * (1 + g / 100.0) ** k for k in range(1, 5)]
            return tri(flux(cours, s2, ctx)[0])
        lo, hi = -50.0, 60.0
        flo = tri_g(lo)
        if num(flo):
            for _ in range(80):
                mid = (lo + hi) / 2
                t_ = tri_g(mid)
                if not num(t_):
                    break
                if t_ < (R.get('tx') or 15.0):
                    lo = mid
                else:
                    hi = mid
            R['g_exigee'] = (lo + hi) / 2

    # V22.4 : ancrage terminal indépendant du cours. Aucun repli sur mact.
    ancrage = valo.get('ancrage_terminal') or {}
    plafond = ancrage.get('plafond')
    valide = (num(plafond) and plafond > 0 and bool(ancrage.get('date'))
              and bool(ancrage.get('justification')))
    R['R_plafond'] = plafond if valide else None
    R['ancrage_valide'] = bool(valide)
    clause = (valo.get('clause') or 'aucune').upper()
    R['clause'] = clause
    R['R_depasse'] = bool(valide and C['multiple'] > plafond + 1e-9)
    R['valorisation_valide'] = bool(valide and not R['R_depasse'] and clause == 'AUCUNE')
    if not R['valorisation_valide']:
        warn('Prix indicatif : ancrage terminal absent/invalide, plafond dépassé ou ancienne clause à migrer en V22.4.')
    chk('Ancrage terminal indépendant du cours', 'validé' if R['valorisation_valide'] else 'échec',
        str(ancrage.get('justification') or 'Renseigner valo.ancrage_terminal : plafond, date, justification.'))
    # Empreinte reproductible des hypothèses, hors cours et diagnostics de marché.
    empreinte = {'base': base, 'scenarios': scs, 'contexte': ctx, 'taux': R['tx'],
                 'ancrage': ancrage, 'tob': TOB, 'tax_pv': TAX_PV,
                 'date_eval': meta.get('date_eval'), 'version': VERSION}
    R['empreinte_hypotheses'] = hashlib.sha256(json.dumps(empreinte, sort_keys=True,
        ensure_ascii=False).encode()).hexdigest()[:16]

    # momentum, taille, tranches
    mom = D.get('momentum') or {}
    p6, mm = mom.get('perf6m_rel'), mom.get('vs_mm200')
    if num(p6) and num(mm):
        R['momentum'] = 'FAVORABLE' if (p6 > 0 and mm > 0) else 'D\u00c9FAVORABLE' if (p6 < 0 and mm < 0) else 'MIXTE'
    else:
        R['momentum'] = 'IND\u00c9TERMIN\u00c9'

    Q = R['q']['Q']; fiab = (meta.get('fiabilite') or 'B').upper()[:1]
    pari = False
    lim = []
    if num(Q) and Q >= 70:
        capQ = 6 if Q >= 90 else 5 if Q >= 85 else 4 if Q >= 80 else 3
        fac = {'A': 1, 'B': 1, 'C': 0.7, 'D': 0}.get(fiab, 1)
        if pari:
            fac = min(fac, 0.7)
        lim.append(('qualit\u00e9 ajust\u00e9e', capQ * fac))
    vis = R['q']['vis']
    if num(vis) and vis < 50:
        lim.append(('visibilit\u00e9 <50 %', 2))
    L = max(0.0, 1 - R['cap_cours'] / 100) if num(R['cap_cours']) else None
    if num(L) and L > 0:
        lim.append(('budget de perte 1,5 %', 1.5 / L))
    liq = meta.get('liquidite_max_pct')
    if num(liq):
        lim.append(('liquidit\u00e9', liq))
    R['taille'] = {'limites': lim, 'max': min([v for _, v in lim]) if lim else None,
                   'contrainte': min(lim, key=lambda t: t[1])[0] if lim else None,
                   'provisoire': not num(liq)}
    R['tranches'] = '50 / 25 / 25 %' if (R['momentum'] == 'FAVORABLE' and fiab != 'C' and not pari) else '1/3 \u2013 1/3 \u2013 1/3'
    R['tranche1'] = 'au prix admissible (≤ prix d’achat) ; exposition au multiple à examiner séparément'
    R['priorite'] = ('ACTIF' if cours <= R['PJ'] else 'VEILLE') if num(R.get('PJ')) and R['PJ'] > 0 else 'non \u00e9valu\u00e9e'
    R['porte_prix'] = 'ouverte' if (num(R.get('PA')) and cours <= R['PA']) else ('PROCHE' if (num(R.get('PJ')) and cours <= R['PJ']) else 'LOIN')

    ach = (G(D, 'verdict.achat') or '').upper()
    # --- verdict final : le moteur neutralise un ACHAT que les controles interdisent
    vf, motifs = (G(D, 'verdict.achat') or 'n.d.'), []
    veut_acheter = ('ACHAT' in ach or 'RENFORCEMENT' in ach) and 'BLOQU' not in ach
    if q_bloc := (D.get('qualite') or {}).get('blocage'):
        vf, _ = 'REJET \u2014 STRUCTURE', motifs.append('blocage structurel d\u00e9clar\u00e9')
    elif fiab == 'D':
        vf, _ = '\u00c0 DOCUMENTER \u2014 ACHAT BLOQU\u00c9', motifs.append('fiabilit\u00e9 D')
    elif not R['valorisation_valide']:
        vf, _ = 'À DOCUMENTER — ACHAT BLOQUÉ', motifs.append('ancrage terminal non validé')
    elif veut_acheter and not R['q']['porte']:
        vf, _ = 'HORS S\u00c9LECTION', motifs.append('porte qualit\u00e9 non franchie')
    elif veut_acheter and R['porte_prix'] != 'ouverte':
        vf = 'WATCHLIST %s \u2014 PRIX' % ('PROCHE' if R['porte_prix'] == 'PROCHE' else 'LOIN')
        motifs.append('cours au-dessus du prix d\'achat')
    elif veut_acheter and num(R.get('part_mult')) and R['part_mult'] > 50:
        vf, _ = 'WATCHLIST \u2014 CONFIRMATION', motifs.append('part du multiple >50 %')
    elif veut_acheter and num(R.get('tx_brut')) and R['tx_brut'] > TX_MAX + 1e-9:
        vf, _ = 'HORS S\u00c9LECTION', motifs.append('risque au-del\u00e0 de 21 %')
    R['verdict_final'] = vf
    R['verdict_motifs'] = motifs
    R['verdict_modifie'] = (str(vf).upper() != ach)
    if R['verdict_modifie']:
        warn('Verdict %s remplac\u00e9 par %s : %s.' % (G(D, 'verdict.achat'), vf, ' ; '.join(motifs)))
    chk('Verdict final contr\u00f4l\u00e9 par le moteur', 'valid\u00e9',
        'inchang\u00e9' if not R['verdict_modifie'] else 'corrig\u00e9 \u2014 %s' % ' ; '.join(motifs))
    if 'ACHAT' in ach and 'BLOQU' not in ach and R['porte_prix'] != 'ouverte':
        warn('Verdict ACHAT alors que le cours est au-dessus du prix d\'achat (taux exig\u00e9 %s %%) : incoh\u00e9rent.' % fr(R.get('tx'), 1))
        chk('Coh\u00e9rence verdict / porte prix', '\u00e9chec', 'ACHAT au-dessus du prix d\'achat')
    else:
        chk('Coh\u00e9rence verdict / porte prix', 'valid\u00e9')
    if num(R['part_mult']) and R['part_mult'] > 50 and ach.startswith('ACHAT'):
        warn('Part du multiple >50 % : pari de revalorisation, pas d\'ACHAT standard.')
    chk('TRI, prix et capital pr\u00e9serv\u00e9 calcul\u00e9s par le moteur', 'valid\u00e9')
    R['calc'] = True
    return R


# ------------------------------------------------------------------ these
def compter_these(t):
    mots = [m for m in re.split(r'\s+', (t or '').strip()) if re.search(r'[0-9A-Za-z\u00c0-\u00ff]', m)]
    phr = [p for p in re.split(r'[.!?]+', t or '') if p.strip()]
    return len(mots), len(phr)


# ------------------------------------------------------------------ rendu HTML
def esc(s):
    return html.escape('' if s is None else str(s), quote=True)


def lvc(l):
    return 'ldoc' if l == 'doc' else ('lgris' if l == 'gris' else 'l%s' % l)


def bdg(t, l, extra=''):
    return '<span class="b %s %s">%s</span>' % (lvc(l), extra, esc(t))


def prov(p):
    return '<sup class="pv">%s</sup>' % esc(p) if p else ''

CSS = """
:root{--l6:#4ede9a;--l5:#4ede9a;--l4:#f2cf5b;--l3:#f0994a;--l2:#f0605f;--l1:#e0403f;--gris:#7e979d;
--bg:#000;--carte:#0c1113;--bord:#2b3d42;--bord2:#1d2a2e;--txt:#e8f2f4;--txt2:#a9c0c5;--cy:#39d6e0;--cy2:#0f8f99;
box-sizing:border-box;padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}
*,*::before,*::after{box-sizing:inherit}
html{scroll-padding-top:env(safe-area-inset-top,0px)}
body{margin:0;background:var(--bg);color:var(--txt);
font-family:"Iowan Old Style","Charter",Georgia,serif;font-size:18px;line-height:1.62;
background-image:linear-gradient(var(--bord2) 1px,transparent 1px),linear-gradient(90deg,var(--bord2) 1px,transparent 1px);
background-size:64px 64px;background-position:-1px -1px}
.wrap{max-width:1220px;margin:0 auto;padding:34px 24px 80px}
h1{font-size:40px;line-height:1.12;margin:0 0 6px;font-weight:600;letter-spacing:-.015em}
h2{font-size:15px;margin:52px 0 16px;font-weight:600;color:var(--cy);
font-family:ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.02em}
h3{font-size:20px;margin:0 0 12px;font-weight:600;color:var(--txt)}
p{margin:0 0 16px;max-width:68ch}
.c{background:var(--carte);border:1px solid var(--bord);border-radius:14px;padding:24px 26px;margin-bottom:18px}
.grid{display:grid;gap:16px}
.g4{grid-template-columns:repeat(4,1fr)}.g3{grid-template-columns:repeat(3,1fr)}
.g2{grid-template-columns:repeat(2,1fr)}.g5{grid-template-columns:repeat(5,1fr)}
.head{display:flex;flex-wrap:wrap;justify-content:space-between;align-items:flex-start;gap:24px;
border-left:3px solid var(--cy);padding:4px 0 4px 22px;margin-bottom:30px}
.cours{font-size:46px;color:var(--cy);font-weight:600;line-height:1;letter-spacing:-.02em;
font-family:ui-monospace,SFMono-Regular,Menlo,monospace;text-align:right;white-space:nowrap}
.sub{color:var(--txt2);font-size:15px;line-height:1.5;margin-top:8px;max-width:70ch}
.big{font-size:34px;font-weight:600;line-height:1;letter-spacing:-.02em;margin:10px 0 0;
font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-variant-numeric:tabular-nums}
.lab{color:var(--gris);font-size:14px;line-height:1.35}
.b{display:inline-block;padding:5px 13px;border-radius:999px;font-size:14px;font-weight:600;color:#04100f;
background:var(--gris);white-space:nowrap;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
.b.l6,.b.l5{background:var(--l5)}.b.l4{background:var(--l4)}.b.l3{background:var(--l3)}
.b.l2{background:var(--l2)}.b.l1{background:var(--l1);color:#fff}
.b.lgris{background:var(--gris)}.b.ldoc{background:transparent;color:var(--l3);border:1px solid var(--l3)}
.b.gros{font-size:16px;padding:7px 17px}
.t6,.t5{color:var(--l5)}.t4{color:var(--l4)}.t3{color:var(--l3)}.t2{color:var(--l2)}.t1{color:var(--l1)}
.tgris,.tdoc{color:var(--gris)}
table{width:100%;border-collapse:collapse;font-size:16px;font-variant-numeric:tabular-nums}
th,td{text-align:left;padding:13px 12px;border-bottom:1px solid var(--bord2);vertical-align:top}
th{color:var(--gris);font-weight:500;font-size:14px}
td.n,th.n{text-align:right;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
tbody tr:last-child td{border-bottom:none}
.scroll{overflow-x:auto}
.bar{height:11px;background:#16211f;border-radius:6px;overflow:hidden;margin-top:6px}
.bar i{display:block;height:100%;border-radius:6px}
.pv{color:var(--cy);font-size:11px;margin-left:3px}
.rl{position:relative;height:140px;margin:44px 0 22px}
.rl .seg{position:absolute;top:34px;height:30px}
.rl .seg:first-of-type{border-radius:8px 0 0 8px}.rl .seg:last-of-type{border-radius:0 8px 8px 0}
.rl .cur{position:absolute;top:0;transform:translateX(-50%);color:var(--cy);font-size:16px;font-weight:600;
white-space:nowrap;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
.rl .tick{position:absolute;top:70px;transform:translateX(-50%);font-size:14px;color:var(--txt2);
white-space:nowrap;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
tr.scn td{border-bottom:2px solid var(--bord2);padding:0 12px 18px;font-size:15px;line-height:1.6;color:var(--txt2)}
tr.scn+tr td{padding-top:18px}
table.sc td,table.sc th{padding:14px 14px}
ul{margin:0;padding:0;list-style:none}
li{position:relative;padding-left:28px;margin-bottom:16px;font-size:16.5px;line-height:1.6;max-width:70ch}
li::before{position:absolute;left:0;top:0;font-weight:700;font-size:18px}
.plus li::before{content:"+";color:var(--l5)}.moins li::before{content:"\u2013";color:var(--l2)}
.concl{border:1px solid var(--cy2);border-radius:14px;padding:30px 32px;
background:linear-gradient(160deg,rgba(57,214,224,.09),rgba(57,214,224,.015) 55%,transparent)}
.concl p{font-size:19px;line-height:1.6}
.nico{border:1px dashed var(--cy2);border-radius:10px;padding:14px 16px;font-size:14px;color:var(--cy);
word-break:break-all;background:#04100f;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
details{border-top:1px solid var(--bord2);padding-top:12px;margin-top:12px}
summary{cursor:pointer;color:var(--txt2);font-size:15px}
.chart{display:flex;align-items:flex-end;gap:6px;height:130px;margin-top:12px}
.chart div{flex:1;background:var(--cy);border-radius:3px 3px 0 0;min-height:1px;position:relative}
.chart div.e{background:repeating-linear-gradient(45deg,var(--cy2),var(--cy2) 4px,#0c1113 4px,#0c1113 8px)}
.xl{display:flex;gap:6px;font-size:13px;color:var(--gris);margin-top:6px}.xl span{flex:1;text-align:center}
.capital-box{border-color:var(--cy2)}.margin-box{border-color:#547547}
.capital-box h3{color:var(--cy)}.margin-box h3{color:var(--l5)}
.capital-box th,.margin-box th{color:var(--txt2);width:32%}
.capital-box .b,.margin-box .b{white-space:normal}
:focus-visible{outline:2px solid var(--cy);outline-offset:2px}
@media(max-width:820px){.g4,.g3,.g5,.g2{grid-template-columns:1fr 1fr}h1{font-size:32px}.cours{font-size:34px}}
@media(max-width:480px){.g4,.g3,.g5,.g2{grid-template-columns:1fr}.head{flex-direction:column}
body{font-size:17px}.cours{text-align:left}}
@media print{body{background:#fff;color:#000;background-image:none}.c,.concl{border-color:#999}.b{border:1px solid #333}}
"""


def carte(lab, valeur, lvl, sous=''):
    return ('<div class="c"><div class="lab">%s</div><div class="big t%s">%s</div>'
            '<div class="sub">%s</div></div>' % (esc(lab), lvl if lvl != 'gris' else 'gris', valeur, sous))


# Encadrés de lecture uniquement : aucun effet sur calculs, scores ou portes.
def qual_texte(value):
    v = V(value)
    return esc(v['v'] if v['v'] not in (None, '') else 'n.d.') + (
        '<div class="sub">%s</div>' % esc(' · '.join(str(v[k]) for k in ('prov', 'src', 'note') if v[k]))
        if any(v[k] for k in ('prov', 'src', 'note')) else '')


def qual_badge(value):
    lab = vv(value) or 'INCONNUE'
    levels = {'STABLE': 5, 'STABLES': 5, 'EN HAUSSE': 5, 'EN AMÉLIORATION': 5,
              'EN BAISSE': 3, 'ÉROSION': 3, 'VOLATILE': 4,
              'SOUS LE COÛT DU CAPITAL': 2, 'NON PERTINENTE': 'gris'}
    return bdg(lab, levels.get(lab, 'gris'))


def qual_serie(serie):
    # Ne pas inventer de points ni convertir une absence en zéro.
    rows = []
    for item in (serie or []):
        if not isinstance(item, (list, tuple)) or len(item) < 2:
            continue
        val = vv(item[1])
        if not num(val) or not math.isfinite(val):
            val = None
        rows.append('<tr><td>%s</td><td class="n">%s</td><td>%s</td></tr>' % (
            esc(item[0]), fr(val) + ' %' if val is not None else 'n.d.',
            esc(' · '.join(str(x) for x in item[2:] if x is not None))))
    return ('<div class="scroll"><table><tr><th>Exercice</th><th class="n">Valeur</th>'
            '<th>Provenance / source</th></tr>%s</table></div>' % ''.join(rows)) if rows else '<p class="sub">Historique non documenté.</p>'


def encadres_qualite(D, R):
    rent = D.get('rentabilite') or {}
    mg = G(D, 'qualite.marge_brute') or {}
    rb = R['rentab']
    rows = [
        ('Combien rapporte la machine ?', 'Dernier ROIC : %s %% · médiane : %s %% · coût du capital : %s %%' % (fr(rb['last']), fr(rb['med']), fr(rb['wacc']))),
        ('Est-elle durable ?', qual_badge(rent.get('tendance')) + qual_texte(rent.get('tendance_preuve'))),
        ('Les nouveaux euros travaillent-ils aussi bien ?', qual_badge(rent.get('nouveaux_investissements')) + qual_texte(rent.get('rendement_incremental'))),
        ('Peut-elle grossir ?', qual_texte(rent.get('reinvestissement'))),
        ('Le chiffre est-il trompeur ?', qual_texte(rent.get('vigilance_comptable'))),
    ]
    a = '<section class="c capital-box"><h3>La machine à créer du profit</h3><p class="sub">Chaque euro supplémentaire investi crée-t-il suffisamment de profit après impôt, et combien peut-on encore investir ainsi ?</p><table>'
    a += ''.join('<tr><th>%s</th><td>%s</td></tr>' % (esc(k), v) for k, v in rows)
    a += '</table><details><summary>Historique du ROIC et sources</summary>' + qual_serie(rent.get('roic')) + qual_texte(rent.get('source')) + '</details><p class="sub">ROIC après impôt ; AT ROCE comparable seulement à définition cohérente. Rentabilité économique ≠ rendement boursier.</p></section>'
    a += '<section class="c margin-box"><h3>Marge brute — maîtrise de son environnement</h3>'
    a += qual_badge(mg.get('tendance')) + '<p class="sub">La marge est un indice de pouvoir de prix, pas une preuve suffisante de domination.</p>'
    a += qual_serie(mg.get('serie'))
    a += '<table>' + ''.join('<tr><th>%s</th><td>%s</td></tr>' % (label, qual_texte(mg.get(key))) for label, key in [
        ('Définition et comparabilité', 'definition'), ('Prix, coûts, volumes et mix', 'explication'),
        ('Pouvoir de prix : preuves et limites', 'pouvoir_prix_preuve'),
        ('Position concurrentielle', 'conclusion'), ('À surveiller', 'surveillance')]) + '</table>'
    a += '<p class="sub">Une baisse modérée appelle une explication, sans veto automatique. Aucun score supplémentaire ; faits rattachés aux piliers existants.</p></section>'
    return a


def rendu(D, R):
    meta = D.get('meta') or {}
    valo = D.get('valo') or {}
    cours = vv(meta.get('cours')); dev = meta.get('devise', '')
    out = []
    A = out.append
    A('<!doctype html><html lang="fr"><head><meta charset="utf-8">')
    A('<meta name="viewport" content="width=device-width,initial-scale=1">')
    A('<title>Dossier %s \u2014 %s</title><style>%s</style></head><body><div class="wrap">' % (
        esc(meta.get('societe')), esc(meta.get('ticker')), CSS))

    # -- en-tete
    A('<div class="head"><div><h1>%s</h1><div class="sub">%s \u00b7 %s \u00b7 %s \u00b7 %s</div>'
      '<div class="sub">Mode %s \u00b7 \u00e9valu\u00e9 le %s \u00b7 %s \u00b7 fiabilit\u00e9 %s \u00b7 taux exig\u00e9 %s %%/an</div></div>'
      '<div><div class="cours">%s %s</div><div class="sub">cours du %s</div></div></div>' % (
          esc(meta.get('societe')), esc(meta.get('ticker')), esc(meta.get('bourse')), esc(meta.get('secteur')),
          esc(meta.get('pays')), esc(meta.get('mode', 'nouvelle position')), esc(meta.get('date_eval')), VERSION,
          esc(meta.get('fiabilite')), fr(R.get('tx'), 1), fprix(cours), esc(dev), esc(meta.get('date_cours'))))

    # -- audit de revision : textes et tableaux fournis avec l'instantane.
    audit = D.get('audit_valorisation') or {}
    if audit:
        A('<div class="c"><h3 style="color:var(--cy)">Valorisation corrigée · hypothèses explicites</h3>')
        A('<p>%s</p>' % esc(audit.get('resume')))
        for titre, lignes in (audit.get('tableaux') or {}).items():
            A('<h3 style="color:var(--l4)">%s</h3><div class="scroll"><table>' % esc(titre))
            for i, ligne in enumerate(lignes):
                balise = 'th' if i == 0 else 'td'
                A('<tr>' + ''.join('<%s>%s</%s>' % (balise, esc(c), balise) for c in ligne) + '</tr>')
            A('</table></div>')
        for note in audit.get('notes') or []:
            A('<p class="sub">%s</p>' % esc(note))
        A('<p class="sub">Empreinte des hypothèses : %s. Un autre cours ne modifie pas cette empreinte.</p></div>' % esc(R.get('empreinte_hypotheses')))
    if R.get('calc') and not R.get('valorisation_valide'):
        A('<div class="c" style="border-color:var(--l2)">Prix indicatifs uniquement : ancrage terminal à corriger avant toute décision.</div>')
    # -- verdict
    v = D.get('verdict') or {}
    A('<div class="c"><div>%s &nbsp; %s</div><p style="margin-top:10px;font-size:16px">%s</p>'
      '<div class="sub">%s%s</div></div>' % (
          bdg(R.get('verdict_final') or v.get('achat', 'n.d.'), L_LAB('achat', R.get('verdict_final')), 'gros'),
          bdg(v.get('suivi', 'n.d.'), L_LAB('suivi', v.get('suivi')), 'gros'),
          esc(v.get('phrase')), esc(v.get('cause')),
          ' \u00b7 ' + esc(v.get('cause2')) if v.get('cause2') else ''))
    if R.get('verdict_modifie'):
        A('<div class="c" style="border-color:var(--l3)"><b>Verdict corrig\u00e9 par le moteur.</b> '
          'Le dossier proposait \u00ab %s \u00bb ; les contr\u00f4les l\'interdisent : %s.</div>' % (
              esc(v.get('achat')), esc(' ; '.join(R.get('verdict_motifs') or []))))

    # -- 4 cartes
    q = R['q']
    A('<div class="grid g4">')
    A(carte('Qualit\u00e9 (couverture %s %%)' % fr(q['cov'], 0),
            '%s %%' % fr(q['Q'], 0), q['niveau'],
            ('provisoire' if q['provisoire'] else 'porte qualit\u00e9 %s' % ('franchie' if q['porte'] else 'non franchie'))))
    A(carte('Croissance centrale par action', '%s %%/an' % fr(R['gc'], 1), L_PCT(R['C']) if num(R['C']) else 'gris',
            'score C %s %% (descriptif)' % fr(R['C'], 0)))
    A(carte('Rendement net retenu (seuil %s %%)' % fr(R.get('tx'), 1), '%s %%/an' % fr(R.get('retenu'), 1),
            R.get('niv_retenu', 'gris'),
            'central %s %% \u00b7 pond\u00e9r\u00e9 %s %%' % (fr(R.get('tri_central'), 1), fr(R.get('tri_pondere'), 1))))
    A(carte('Capital pr\u00e9serv\u00e9 / 100 \u20ac', fr(R.get('cap_cours'), 0), R.get('niv_cap', 'gris'),
            'baissier \u00e0 4 ans, au cours \u2014 sc\u00e9nario mod\u00e9lis\u00e9'))
    A('</div>')

    mr = ''.join('<tr><td>%s</td><td class="n t%s">%s pt</td></tr>' % (
        esc(lab), 5 if d < 0 else 3, fr(d, 1, True)) for lab, d in (R.get('tx_mods') or []))
    if not mr:
        mr = '<tr><td>aucun modificateur retenu</td><td class="n">0 pt</td></tr>'
    A('<div class="c"><h3>Taux exig\u00e9 de la ligne \u2014 %s %%/an</h3>'
      '<div class="sub">Base 15 %%, born\u00e9 12\u201321 %%. Ce taux ne facture que le risque '
      '<b>non mod\u00e9lisable dans les flux</b> (juridiction, liquidit\u00e9, perte irr\u00e9versible) : '
      'ce qui est d\u00e9j\u00e0 chiffr\u00e9 dans le sc\u00e9nario baissier ou dans le multiple terminal n\'y figure pas (R3).</div>'
      '<div class="scroll"><table>%s<tr><td><b>Taux exig\u00e9 retenu</b></td><td class="n"><b>%s %%</b></td></tr></table></div>%s</div>' % (
          fr(R.get('tx'), 1), mr, fr(R.get('tx'), 1),
          '<div class="sub">Valeur born\u00e9e \u00e0 l\'intervalle 12\u201321 %.</div>' if R.get('tx_borne') else ''))

    A('<div class="sub" style="margin:6px 0 14px">Tri rapide : %s. Les scores sont des conventions de s\u00e9lection en %%, pas des probabilit\u00e9s.</div>' % esc(meta.get('tri')))

    # -- ACTE 0
    a0 = D.get('acte0') or {}
    th = a0.get('these') or {}
    nbm, nbp = compter_these(th.get('texte'))
    rev = ''.join('<tr><td>%s</td><td class="n">%s</td><td class="n">%s</td><td>%s</td></tr>' % (
        esc(r[0]), esc(r[1]), esc(r[2] if len(r) > 2 else ''), prov(r[3] if len(r) > 3 else '')) for r in (a0.get('revenus') or []))
    lignes = []
    lignes.append(('Rendement au cours du jour', '%s %%/an' % fr(R.get('retenu'), 1), R.get('niv_retenu', 'gris')))
    lignes.append(('Prix d\'achat (taux exig\u00e9 %s %%)' % fr(R.get('tx'), 1), '%s %s' % (fprix(R.get('PA')), dev), 5))
    ec = R.get('ecart_PA')
    lignes.append(('\u00c9cart \u00e0 franchir', '%s %%' % fr(ec, 1, True), 5 if (num(ec) and ec <= 0) else 3))
    if (valo.get('clause') or 'aucune').lower() != 'aucune':
        lignes.append(('Rendement central \u00e0 multiple constant', '%s %%/an' % fr(R.get('tri_mult_constant'), 1), L_RDT(R.get('tri_mult_constant'))))
    lh = ''.join('<tr><td>%s</td><td class="n t%s">%s</td></tr>' % (esc(l), n if n != 'gris' else 'gris', vtxt) for l, vtxt, n in lignes)
    A('<div class="grid g2">')
    A('<div class="c"><h3>Ce qu\'elle fait</h3>'
      '<p><b>Activit\u00e9</b> \u2014 %s</p><p><b>Positionnement</b> \u2014 %s</p><p><b>Perspectives</b> \u2014 %s</p>'
      '<div class="scroll"><table>%s</table></div><div class="sub">%s %s</div></div>' % (
          esc(a0.get('activite')), esc(a0.get('positionnement')), esc(a0.get('perspectives')), rev,
          esc(V(a0.get('ratio_echelle'))['v']), prov(V(a0.get('ratio_echelle'))['prov'])))
    A('<div class="c"><h3>La th\u00e8se en 80 mots</h3><p>%s</p>'
      '<div class="sub">%s mots \u00b7 %s phrases%s</div><table>%s</table></div>' % (
          esc(th.get('texte')), nbm, nbp,
          '' if (nbm <= 80 and 3 <= nbp <= 4) else ' \u2014 <span class="t3">hors format</span>', lh))
    A('</div>')

    # -- bande compacte
    sec = D.get('secteur') or {}
    rb = R['rentab']
    st = G(D, 'risques.stress') or {}
    d_pire = min([x for x in (st.get('d_bas'), st.get('d_haut')) if num(x)] or [None]) if any(num(st.get(k)) for k in ('d_bas', 'd_haut')) else None
    A('<div class="grid g4">')
    A('<div class="c"><div class="lab">Vent sectoriel</div><div>%s</div><div class="sub">%s \u00b7 %s %s</div></div>' % (
        bdg('%s \u00e0 %s %%/an' % (fr(sec.get('s_bas'), 1), fr(sec.get('s_haut'), 1)), L_SECT(sec.get('s_bas'))),
        esc(sec.get('perimetre')), esc(sec.get('periode')), prov(sec.get('prov'))))
    A('<div class="c"><div class="lab">Rentabilit\u00e9 \u00e9conomique</div><div>%s</div>'
      '<div class="sub">m\u00e9diane %s %% \u00b7 min %s %% \u00b7 %s</div></div>' % (
          bdg(rb['lab'], rb['lvl']), fr(rb['med'], 1), fr(rb['min'], 1),
          bdg(V(G(D, 'rentabilite.nouveaux_investissements'))['v'] or 'INCONNUS',
              L_LAB('invest', V(G(D, 'rentabilite.nouveaux_investissements'))['v']))))
    A('<div class="c"><div class="lab">Stress pouvoir d\'achat \u221220 %%</div><div>%s</div><div class="sub">%s</div></div>' % (
        bdg('%s \u00e0 %s %% de r\u00e9sultat op. an 4' % (fr(st.get('d_bas'), 0), fr(st.get('d_haut'), 0)), L_D(d_pire)),
        esc(st.get('mecanisme'))))
    ial = V(G(D, 'risques.ia'))['v']
    A('<div class="c"><div class="lab">Effet de l\'IA sur ce m\u00e9tier</div><div style="margin-top:8px">%s</div>'
      '<div class="sub">%s</div></div>' % (bdg(ial or 'IND\u00c9TERMIN\u00c9', L_LAB('ia', ial), 'gros'),
                                          esc(V(G(D, 'risques.ia'))['src'] or '')))
    A('</div>')

    pp = V(G(D, 'qualite.pouvoir_prix'))
    if pp['v'] and any(s in str(pp['v']).upper() for s in ('FORT', 'INT\u00c9GRAL')):
        A('<div class="c" style="border-color:var(--l5)"><h3>Pouvoir de prix \u2014 test +10 %%</h3><div>%s</div><p>%s</p></div>' % (
            bdg(pp['v'], L_LAB('prix', pp['v']), 'gros'), esc(pp['prov'] or pp['src'] or G(D, 'qualite.pouvoir_prix_preuve'))))

    # ---------------- bloc 1
    A('<h2>Ce qui peut casser la th\u00e8se</h2>')
    res = D.get('resultats') or {}
    rp = res.get('reperes') or {}
    cells = ''.join('<td class="n">%s %%</td>' % fr(rp.get(k), 1, True) for k in ('ca_n1', 'ca_attentes', 'bpa_n1', 'bpa_attentes'))
    A('<div class="c"><h3>Derniers r\u00e9sultats et guidance</h3><div>%s</div>'
      '<div class="scroll"><table><tr><th class="n">CA vs N\u22121</th><th class="n">CA vs attentes</th>'
      '<th class="n">BPA vs N\u22121</th><th class="n">BPA vs attentes</th></tr><tr>%s</tr></table></div>'
      '<p>%s</p><div class="sub">Confirmations : %s</div></div>' % (
          bdg(res.get('verdict', 'IND\u00c9TERMIN\u00c9'), L_LAB('resultats', res.get('verdict'))), cells,
          esc(res.get('guidance') or res.get('commentaire')), esc(' \u00b7 '.join(res.get('confirmations') or []))))
    rows = ''.join('<tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>' % (
        esc(r.get('fait')), esc(r.get('mecanisme')), esc(r.get('gravite')), esc(r.get('indicateur')), esc(r.get('hypothese')))
        for r in (G(D, 'risques.registre') or []))
    A('<div class="c"><h3>Registre des risques</h3><div class="scroll"><table>'
      '<tr><th>Fait</th><th>M\u00e9canisme</th><th>Gravit\u00e9</th><th>Indicateur avanc\u00e9</th><th>Hypoth\u00e8se</th></tr>%s</table></div>'
      '<div style="margin-top:10px">%s %s</div><div class="sub">%s</div></div>' % (
          rows, bdg('IA : %s' % (ial or 'IND\u00c9TERMIN\u00c9'), L_LAB('ia', ial)),
          bdg('Cycle capex IA : %s' % (V(G(D, 'risques.capex_ia'))['v'] or 'IND\u00c9TERMIN\u00c9'),
              L_LAB('capex', V(G(D, 'risques.capex_ia'))['v'])),
          esc(V(G(D, 'risques.ia'))['prov'])))

    # ---------------- bloc 2
    A('<h2>La qualit\u00e9 du business, et ce qui le fait grandir</h2>')
    barres = []
    for k, lab, w in PIL:
        p = q['pil'][k]
        lv = L_PCT(p['pct'])
        barres.append('<div style="margin-bottom:9px"><div class="sub">%s /%s &nbsp; <b class="t%s">%s</b>%s</div>'
                      '<div class="bar"><i style="width:%s%%;background:var(--%s)"></i></div></div>' % (
                          esc(lab), w, lv if lv != 'gris' else 'gris',
                          ('%s %%' % fr(p['pct'], 0)) if p['pct'] is not None else 'n.d.',
                          '' if p['obs'] == 3 else ' \u2014 %s/3 contr\u00f4les, PARTIEL' % p['obs'],
                          max(0, min(100, p['pct'] or 0)), lvc(lv).replace('l', 'l') if lv != 'gris' else 'gris'))
    inconnus = G(D, 'qualite.inconnus') or []
    A('<div class="grid g2"><div class="c"><h3>Six piliers</h3>%s<div class="sub">Q = %s %% \u00b7 couverture %s %%%s</div></div>' % (
        ''.join(barres), fr(q['Q'], 0), fr(q['cov'], 0),
        ' \u00b7 contr\u00f4les inconnus : ' + esc(', '.join(inconnus)) if inconnus else ''))
    vals = rb['vals']
    graph = ''
    if vals:
        mx = max(vals + ([rb['wacc']] if num(rb['wacc']) else []))
        graph = '<div class="chart">%s</div><div class="xl">%s</div>' % (
            ''.join('<div style="height:%s%%"></div>' % max(2, 100 * v / mx if mx else 0) for v in vals),
            ''.join('<span>%s</span>' % esc(a) for a in rb['annees']))
    A('<div class="c"><h3>Rentabilit\u00e9 \u00e9conomique \u2014 niveau et stabilit\u00e9</h3><div>%s</div>%s'
      '<div class="sub">m\u00e9diane %s %% \u00b7 min %s %% \u00b7 derni\u00e8re %s %% \u00b7 %s/%s ann\u00e9es &gt; WACC %s %% \u00b7 IQR %s pts</div>'
      '<p class="sub">%s</p></div></div>' % (
          bdg(rb['lab'], rb['lvl'], 'gros'), graph, fr(rb['med'], 1), fr(rb['min'], 1), fr(rb['last'], 1),
          rb['au_dessus'] if rb['au_dessus'] is not None else 'n.d.', rb['n'], fr(rb['wacc'], 1),
          fr(rb['iqr'], 1), esc(G(D, 'rentabilite.definition'))))

    A(encadres_qualite(D, R))

    A('<div class="grid g2"><div class="c"><h3>Moat et pouvoir de prix</h3><p>%s</p><div>%s</div></div>'
      '<div class="c"><h3>Direction, initi\u00e9s et alignement</h3><p>%s</p><div>%s %s %s</div><div class="sub">%s</div></div></div>' % (
          esc(G(D, 'qualite.moat')), bdg(pp['v'] or 'IND\u00c9TERMIN\u00c9', L_LAB('prix', pp['v'])),
          esc(G(D, 'qualite.direction_txt')),
          bdg('Initi\u00e9s : %s' % (V(G(D, 'qualite.inities'))['v'] or 'INFORMATION INDISPONIBLE'),
              L_LAB('inities', V(G(D, 'qualite.inities'))['v'])),
          bdg(V(G(D, 'gouvernance.actionnariat'))['v'] or 'NON DOCUMENT\u00c9',
              L_LAB('actionnariat', V(G(D, 'gouvernance.actionnariat'))['v'])),
          bdg('KPI : %s' % (V(G(D, 'gouvernance.kpi'))['v'] or 'NON PUBLI\u00c9'),
              L_LAB('kpi', V(G(D, 'gouvernance.kpi'))['v'])),
          esc(G(D, 'gouvernance.synthese'))))

    tb = G(D, 'croissance.tableau') or {}
    if tb.get('annees'):
        ne = tb.get('n_estime', 0)
        thh = ''.join('<th class="n">%s</th>' % esc(a) for a in tb['annees'])
        trs = ''
        for nom, serie in (tb.get('lignes') or []):
            trs += '<tr><td>%s</td>%s</tr>' % (esc(nom), ''.join(
                '<td class="n%s">%s</td>' % (' tgris' if (ne and i >= len(tb['annees']) - ne) else '', fr(x, 1) if num(x) else 'n.d.')
                for i, x in enumerate(serie)))
        A('<div class="c"><h3>Trajectoire</h3><div class="scroll"><table><tr><th></th>%s</tr>%s</table></div>'
          '<p>%s</p><p class="sub">%s</p><div>%s</div></div>' % (
              thh, trs, esc(G(D, 'croissance.moteurs')), esc(G(D, 'croissance.convergence')),
              bdg('Protection : %s' % (V(G(D, 'croissance.protection'))['v'] or 'non document\u00e9e'),
                  L_LAB('protection', V(G(D, 'croissance.protection'))['v']))))

    # ---------------- bloc 3
    A('<h2>\u00c0 quel prix cela devient int\u00e9ressant</h2>')
    tol = R.get('tolerance')
    A('<div class="grid g3">%s%s%s</div>' % (
        carte('Rendement au cours du jour', '%s %%/an' % fr(R.get('retenu'), 1), R.get('niv_retenu', 'gris'),
              'seuil de la ligne : %s %%/an' % fr(R.get('tx'), 1)),
        carte('Central contre rythme historique',
              ('%s pts' % fr(R.get('ecart_hist'), 1, True)) if num(R.get('ecart_hist')) else 'n.d.',
              L_ECART(R.get('ecart_hist')),
              'croissance centrale par action moins croissance organique pass\u00e9e'),
        carte('Si le mauvais sc\u00e9nario arrive t\u00f4t', '%s %%/an' % fr(R.get('tri_bear_25'), 1),
              L_RDT(R.get('tri_bear_25')), 'revente forc\u00e9e au bout de 2 ans et demi')))

    # barrette decisionnelle : seulement les niveaux actionnables au-dessus de l'objectif
    PA, PR, PS = R.get('PA'), R.get('PR'), R.get('PS')
    ta = R.get('tx_action') or (15.0, 18.0, 21.0)
    if all(num(x) for x in (PA, PR, PS)):
        hi = max(PA * 1.15, cours * 1.15)
        pc = lambda p: max(0.0, min(100.0, 100 * p / hi))
        segs = [(0, pc(PS), '#2dc7c9'), (pc(PS), pc(PR), '#4ede9a'),
                (pc(PR), pc(PA), '#9edb6b'), (pc(PA), 100, '#f0605f')]
        sg = ''.join('<div class="seg" style="left:%s%%;width:%s%%;background:%s"></div>' % (a, max(0.4, b - a), c) for a, b, c in segs)
        tk = ''.join('<div class="tick" style="left:%s%%;top:%spx">%s \u00b7 %s %% \u00b7 %s</div>' %
                     (pc(p), top, lib, fr(t, 0), fprix(p)) for p, t, lib, top in
                     ((PS, ta[2], 'Forte marge', 70), (PR, ta[1], 'Renfort', 92),
                      (PA, ta[0], 'Objectif', 114)))
        A('<div class="c"><h3>Barrette de prix (%s) \u2014 uniquement les niveaux actionnables</h3><div class="rl">%s%s'
          '<div class="cur" style="left:%s%%">\u25b2 cours %s \u2192 %s %%/an</div></div>'
          '<div class="sub">Objectif %s %% : %s \u00b7 renfort %s %% : %s \u00b7 forte marge %s %% : %s. '
          'Cours du jour : %s \u2192 %s %%/an. Aucun palier sous l\'objectif n\'est affich\u00e9.</div></div>' % (
              esc(dev), sg, tk, pc(cours), fprix(cours), fr(R.get('retenu'), 1),
              fr(ta[0], 0), fprix(PA), fr(ta[1], 0), fprix(PR), fr(ta[2], 0), fprix(PS),
              fprix(cours), fr(R.get('retenu'), 1)))

    srows = ''
    for nom in ('baissier', 'central', 'haussier'):
        sc = (valo.get('scenarios') or {}).get(nom)
        if not sc or 'ctx' not in R:  # arret precoce : pas de scenarios chiffres
            continue
        t_ = tri(flux(cours, sc, R['ctx'])[0])
        pt = sc['bpa'][3] * sc['multiple']
        srows += ('<tr><td><b>%s</b></td><td class="n">%s %%</td><td class="n">%s</td><td class="n">%s\u00d7</td><td class="n">%s</td>'
                  '<td class="n t%s">%s %%/an</td></tr><tr class="scn"><td colspan="6">%s</td></tr>') % (
                     nom.capitalize(), fr(100 * sc.get('poids', POIDS_DEF[nom]), 0), fr(sc['bpa'][3], 2),
                     fr(sc['multiple'], 1), fprix(pt), L_RDT(t_) if L_RDT(t_) != 'gris' else 'gris', fr(t_, 1), esc(sc.get('txt', '')))
    hz = R.get('horizons') or {}
    hrows = ''.join('<tr><td>%s ans</td><td class="n">%s %%</td><td class="n">%s %%</td></tr>' % (
        fr(h, 1), fr(hz[h]['avec'], 1), fr(hz[h]['sans'], 1)) for h in sorted(hz))
    dc = R.get('decomp') or {}
    A('<div class="c"><h3>Trois sc\u00e9narios \u00e0 quatre ans</h3><div class="scroll"><table class="sc">'
      '<tr><th>Sc\u00e9nario</th><th class="n">Poids</th><th class="n">BPA an 4</th><th class="n">Multiple</th>'
      '<th class="n">Prix terminal</th><th class="n">TRI</th></tr>%s</table></div>'
      '<div class="sub">Base publi\u00e9e %s \u2192 base normalis\u00e9e %s \u00b7 %s</div></div>' % (
          srows, fr(vv(valo.get('base_publiee')), 2), fr(vv(valo.get('base_normalisee')), 2), esc(valo.get('effet'))))
    A('<div class="c"><h3>Robustesse du rendement</h3><div class="scroll"><table>'
      '<tr><th>Horizon</th><th class="n">avec revalorisation</th><th class="n">sans</th></tr>%s</table></div>'
      '<div class="sub">D\u00e9composition du TRI central : op\u00e9rations %s %% \u00b7 dividendes %s pts \u00b7 multiple %s pts</div>'
      '<div style="margin-top:8px">%s %s</div>'
      '<div class="sub">Croissance exig\u00e9e pour %s %%/an nets : %s %%/an (inversion m\u00e9canique, seuil indicatif) \u00b7 multiple exig\u00e9 par le cours : %s\u00d7</div>'
      '<div class="sub">Seconde m\u00e9thode : %s</div></div>' % (
          hrows, fr(dc.get('A'), 1), fr(dc.get('div'), 1), fr(dc.get('mult'), 1),
          bdg('Part du multiple %s %%' % fr(R.get('part_mult'), 0), R.get('niv_part', 'gris')),
          bdg('Multiple exig\u00e9 : %s' % R.get('mult_exige_lab', 'n.d.'), L_LAB('mult_exige', R.get('mult_exige_lab'))),
          fr(R.get('tx'), 1), fr(R.get('g_exigee'), 1), fr(R.get('mult_exige'), 1), esc(valo.get('seconde_methode'))))

    # ---------------- bloc 4
    A('<h2>Combien en acheter, et quoi surveiller</h2>')
    tl = R.get('taille') or {}
    A('<div class="c"><h3>Taille, tranches et rythme</h3>'
      '<p>Taille maximale : <b>%s %%</b> du portefeuille%s \u2014 contrainte active : %s.</p>'
      '<p>Tranches %s \u00b7 tranche 1 %s</p><div>%s</div><div class="sub">Capital pr\u00e9serv\u00e9 au prix d\'achat : %s /100 \u00b7 priorit\u00e9 de suivi : %s</div></div>' % (
          fr(tl.get('max'), 1), ' (provisoire : volume inconnu)' if tl.get('provisoire') else '', esc(tl.get('contrainte')),
          esc(R.get('tranches') or 'n.d.'), esc(R.get('tranche1') or 'n.d.'),
          bdg('Momentum : %s' % (R.get('momentum') or 'n.d.'), L_LAB('momentum', R.get('momentum'))),
          fr(R.get('cap_PA'), 0), esc(R.get('priorite') or 'n.d.')))
    lec = D.get('lecture') or {}
    A('<div class="c"><h3>Points forts et points faibles</h3><div class="grid g2">'
      '<ul class="plus">%s</ul><ul class="moins">%s</ul></div></div>' % (
          ''.join('<li>%s</li>' % esc(x) for x in (lec.get('forces') or [])),
          ''.join('<li>%s</li>' % esc(x) for x in (lec.get('faiblesses') or []))))
    pd = lec.get('point_decisif') or {}
    A('<div class="concl"><h3>Conclusion</h3><p>%s</p>'
      '<p><b>Point d\u00e9cisif</b><br>Raison du prix : %s<br>Fondement du d\u00e9saccord : %s<br>'
      'Ce qui nous donnerait tort : %s<br>Marge d\'erreur : %s</p>'
      '<p>Action : %s</p><p>Invalidation : %s</p><p class="sub">Prochain catalyseur : %s</p>'
      '<p>%s \u2014 %s <span class="sub">(\u00e9ch\u00e9ance %s ; non remplie \u2192 \u274c sans nouvelle analyse)</span></p></div>' % (
          esc(lec.get('these_2p')), esc(pd.get('raison_prix')), esc(pd.get('desaccord')), esc(pd.get('tort')),
          esc(pd.get('marge_erreur') or ''), esc(lec.get('action')), esc(lec.get('invalidation')),
          esc(lec.get('catalyseur')), bdg(v.get('suivi', 'n.d.'), L_LAB('suivi', v.get('suivi')), 'gros'),
          esc(v.get('suivi_condition')), esc(v.get('suivi_date'))))

    # ligne NICO + annexes
    A('<h2>Ligne pour l\'outil de tri</h2><div class="nico">%s</div>' % esc(R['nico']))
    src = ''.join('<li>%s%s %s</li>' % (
        esc(s[0]), (' \u2014 <a href="%s" style="color:var(--cy)">lien</a>' % esc(s[1])) if (len(s) > 1 and str(s[1]).startswith(('http://', 'https://'))) else '',
        esc(s[2] if len(s) > 2 else '')) for s in (D.get('sources') or []))
    ctr = ''.join('<tr><td>%s</td><td>%s</td><td>%s</td></tr>' % (esc(c[0]), esc(c[1]), esc(c[2] if len(c) > 2 else ''))
                  for c in (D.get('controles') or []) + [list(x) for x in CHK])
    A('<details><summary>Sources, contr\u00f4les et hypoth\u00e8ses</summary><ul>%s</ul>'
      '<div class="scroll"><table><tr><th>Contr\u00f4le</th><th>\u00c9tat</th><th>Note</th></tr>%s</table></div>'
      '<p class="sub">Fiscalit\u00e9 : net selon les hypoth\u00e8ses indiqu\u00e9es \u2014 plus-value 10 %%, TOB 0,35 %% \u00e0 l\'achat et \u00e0 la vente, '
      'pr\u00e9compte 30 %%, retenue \u00e9trang\u00e8re %s %%. %s</p><p class="sub">%s</p></details>' % (
          src, ctr, fr(100 * (valo.get('retenue_etrangere') or 0), 0), esc(valo.get('fiscalite_note')),
          esc(' \u00b7 '.join(WARN))))
    A('</div></body></html>')
    return ''.join(out)


# ------------------------------------------------------------------ ligne NICO
def ligne_nico(D, R):
    meta = D.get('meta') or {}
    v = D.get('verdict') or {}
    s = (v.get('suivi') or '').upper()
    ach = (R.get('verdict_final') or v.get('achat') or '').upper()
    if meta.get('detenue'):
        st = 'PF'
    elif 'CONSERVER' in s:
        st = 'WL'
    elif 'SURVEILLANCE' in s:
        st = 'SURV'
    elif 'SP\u00c9CULATIVE' in s:
        st = 'SPEC'
    elif 'RETIRER' in s or 'REJET' in ach or 'P\u00c9RIM\u00c8TRE' in ach:
        st = 'OUT'
    else:
        st = 'TODO'
    note = (v.get('nico_note') or v.get('suivi_condition') or '').replace('|', '/')
    ch = ['NICO', meta.get('ticker', ''), meta.get('societe', ''), meta.get('devise', ''), st,
          fprix(R.get('PA')), fprix(vv(meta.get('cours'))), fr(R.get('tx'), 1), fr(R.get('retenu'), 1),
          fr(R.get('cap_cours'), 0), fr(R['q']['Q'], 0), v.get('suivi_date', ''), meta.get('date_eval', ''),
          meta.get('secteur', ''), meta.get('pays', ''), note]
    return ' | '.join(str(c).replace('\u202f', '') for c in ch)


def resume(D, R):
    meta = D.get('meta') or {}; v = D.get('verdict') or {}
    L = ['\U0001f4c4 %s (%s) \u2014 %s' % (meta.get('societe'), meta.get('ticker'), meta.get('date_eval')),
         'Verdict : %s \u2014 %s' % (R.get('verdict_final') or v.get('achat'), v.get('phrase')),
         'Q %s %% (couverture %s %%) \u00b7 C %s %% \u00b7 croissance centrale %s %%/an' % (
             fr(R['q']['Q'], 0), fr(R['q']['cov'], 0), fr(R.get('C'), 0), fr(R.get('gc'), 1)),
         'Taux exig\u00e9 %s %%/an \u00b7 rendement retenu %s %%/an \u00b7 prix d\'achat %s \u00b7 capital pr\u00e9serv\u00e9 %s/100' % (
             fr(R.get('tx'), 1), fr(R.get('retenu'), 1), fprix(R.get('PA')), fr(R.get('cap_cours'), 0)),
         'Central vs historique %s pts \u00b7 sensibilit\u00e9 du prix \u2212%s %% \u00b7 taille max %s %% \u00b7 tranches %s' % (
             fr(R.get('ecart_hist'), 1, True), fr(R.get('tolerance'), 0),
             fr((R.get('taille') or {}).get('max'), 1), R.get('tranches') or 'n.d.'),
         'Suivi : %s \u2014 %s (%s) \u00b7 priorit\u00e9 %s' % (v.get('suivi'), v.get('suivi_condition'),
                                                               v.get('suivi_date'), R.get('priorite') or 'n.d.')]
    if WARN:
        L.append('\u26a0\ufe0f ' + ' \u00b7 '.join(WARN))
    L.append(R['nico'])
    return '\n'.join(L)


def main():
    if len(sys.argv) < 2:
        print(__doc__); sys.exit(1)
    src = sys.argv[1]
    out_dir = sys.argv[3] if len(sys.argv) > 3 and sys.argv[2] == '-o' else os.path.dirname(os.path.abspath(src))
    with open(src, encoding='utf-8') as f:
        D = json.load(f)
    R = calculer(D)
    nbm, nbp = compter_these(G(D, 'acte0.these.texte'))
    if nbm > 80 or not (3 <= nbp <= 4):
        warn('Th\u00e8se : %s mots / %s phrases \u2014 format 3 \u00e0 4 phrases, 80 mots au plus.' % (nbm, nbp))
    R['nico'] = ligne_nico(D, R)
    base = os.path.splitext(os.path.basename(src))[0]
    hp = os.path.join(out_dir, base + '.html')
    with open(hp, 'w', encoding='utf-8') as f:
        f.write(rendu(D, R))
    with open(os.path.join(out_dir, base + '.calc.json'), 'w', encoding='utf-8') as f:
        json.dump({k: val for k, val in R.items() if k not in ('ctx',)}, f, ensure_ascii=False, indent=1, default=str)
    print(resume(D, R))
    print('\nHTML : ' + hp)


if __name__ == '__main__':
    main()
