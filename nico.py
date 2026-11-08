#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""NICO - moteur unique de dossier.

Usage :  python3 nico.py Societe_TICKER_AAAA-MM-JJ.json [-o dossier_sortie]

Fait tout ce qui est mecanique, pour que le modele n'ecrive que des faits et des phrases :
  1. calculs financiers (TRI, flux ponderes, P12/P15/P18, capital preserve, horizons,
     regime alternatif, decomposition du TRI, multiple exige, croissance exigee, taille, tranches)
  2. attribution des niveaux de couleur selon le bareme du fichier A (section 13)
  3. controles automatiques (ordre des prix, residus, garde-fous de clause, coherence du verdict)
  4. rendu HTML autonome fond noir (le livrable)
  5. ligne NICO 17 champs + resume de chat

Aucun appel reseau. Les seuils sont ici ET dans le fichier A : ne jamais modifier l'un sans l'autre.
"""
import json, sys, os, re, math, html, copy, hashlib, datetime, statistics as stx

TOB, TAX_PV = 0.0035, 0.10
POIDS_DEF = {'baissier': .25, 'central': .50, 'haussier': .25}
VERSION = "V25.3"
VERSION_DATE = "08/11/2026"
# Journal des versions archive dans NICO_Historique_Versions.md (hors Projet, sur le PC de Nico).
# V25.3 : débouchés accessibles et capacité de conquête ; contrôle d’autofinancement conservé.
# V25.2 : lecture des derniers résultats dans le pilote et provenance à l'épisode 6.
# V25.1.1 : ordres conditionnes aux donnees fiables, registre obligatoire pour engager en B, plan B conserve jusqu'au changement de voie.
# V25.1 : audit ChatGPT -- une seule consigne (action -> page 1 -> TRI), RENFORCER TACTIQUEMENT (VOIE B), zone d'entree et garde-fous de la Voie B,
#         lignes tactiques du registre (4 places, sorties), pile/face au prix d'entree, VE negative recoupee par action, registre valide.
# V25.0 : page 1 « récit » (titre-verdict, 4 questions, règle des prix, pile/face, plan en 3 étapes), texte centré et plus grand ; lecture.marche_pense / ne_voit_pas / titre.
# V24.1 : registre du portefeuille (NICO_Portefeuille.json) lu automatiquement ; code couleur benefice mauve / FCF turquoise.
VERSION_VALORISATION = "V23.4"  # version des calculs financiers : inchangee tant que prix, taux et tailles sont identiques
CAP_MIN, CAP_SOLIDE, CAP_FORT, CAP_B, CASH_B = 60.0, 70.0, 85.0, 80.0, 20.0
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
    return isinstance(x, (int, float)) and not isinstance(x, bool) and math.isfinite(x)  # V23.2 : infinis rejetes


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
    'pm': {'CATALYSEUR DAT\u00c9': 5, 'CATALYSEUR PROBABLE': 4, 'RENDEMENT PAR LES FLUX': 5,
           'PARI DE REVALORISATION': 3, 'NON DOCUMENT\u00c9': 'gris'},
    'avenir': {'NON DOCUMENT\u00c9': 'gris', 'IND\u00c9TERMIN\u00c9': 'gris', 'EN HAUSSE': 5, 'STABLE': 4,
               'EN BAISSE': 2, 'NON': 1},
    'captation': {'IND\u00c9TERMIN\u00c9': 'gris', 'NON DOCUMENT\u00c9': 'gris', 'CAPT\u00c9E': 5, 'PARTAG\u00c9E': 4,
                  'DISPUT\u00c9E': 3, 'PERDUE': 2},
    'suivi': {'SOUS SURVEILLANCE': 4, 'SP\u00c9CULATIVE': 3, 'CONSERVER': 5, 'RETIRER': 2},
    'fiab': {'A': 6, 'B': 5, 'C': 3, 'D': 1},
    'momentum': {'FAVORABLE': 5, 'D\u00c9FAVORABLE': 3, 'MIXTE': 4, 'IND\u00c9TERMIN\u00c9': 'gris'},
    'mult_exige': {'COMPATIBLE': 5, 'EXIGEANT': 3, 'NON \u00c9TAY\u00c9': 2},
    'resilience': {'ROBUSTE': 5, 'PARI DE R\u00c9GIME': 3, 'SENSIBLE': 4, 'PEU SENSIBLE': 4, 'NON \u00c9VALU\u00c9': 'gris'},
    # V23 : fiche de tri
    'moat': {'LARGE': 5, '\u00c9TROIT': 4, 'ETROIT': 4, 'AUCUN': 2, 'IND\u00c9TERMIN\u00c9': 'gris', 'NON DOCUMENT\u00c9': 'gris'},
    'recurrence': {'R\u00c9CURRENT': 5, 'RECURRENT': 5, 'SEMI-R\u00c9CURRENT': 4, 'SEMI-RECURRENT': 4,
                   'PONCTUEL': 3, 'IND\u00c9TERMIN\u00c9': 'gris', 'NON DOCUMENT\u00c9': 'gris'},
    'cycle': {'NON CYCLIQUE': 5, 'BAS DE CYCLE': 4, 'MILIEU DE CYCLE': 4, 'HAUT DE CYCLE': 2,
              'IND\u00c9TERMIN\u00c9': 'gris', 'NON DOCUMENT\u00c9': 'gris'},
    'ethique': {'CONFORME': 5, '\u00c0 TRANCHER': 3, 'A TRANCHER': 3, 'CONTRAIRE': 1, 'NON DOCUMENT\u00c9': 'gris'},
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


# ------------------------------------------------------------------ V22.9 : initiés
INIT_FORT_PCT = 0.10        # % de la capitalisation, flux net sur 12 mois, achats/ventes de marche
INIT_MIN_EUR = 250000.0     # plancher absolu pour parler de flux fort
INIT_CLUSTER = 3            # acheteurs (ou vendeurs) distincts sur 90 jours = mouvement groupe
INIT_BAS_TIERS = 1 / 3.0    # vente « au plus bas » : prix moyen dans le tiers bas du range 52 semaines
INIT_NATURES_MARCHE = ('MARCH', 'BOURSE', 'OPEN MARKET')


def _nature_marche(n):
    u = _sans_accent(str(n or '')).upper()
    return (not u) or any(k in u for k in ('MARCHE', 'BOURSE', 'OPEN MARKET', 'MARKET'))


def calc_inities(D, R):
    """Flux des dirigeants : achats et ventes faits avec leur propre argent, sur le marche.
    Options exercees, plans, attributions, ventes fiscales : affichees, jamais comptees."""
    meta = D.get('meta') or {}
    ini = D.get('inities') or {}
    txs = ini.get('transactions')
    ref = _date(meta.get('date_eval')) or datetime.date.today()
    capm = vv(meta.get('capitalisation_meur'))
    cours = vv(meta.get('cours'))
    mom = D.get('momentum') or {}
    hi, lo = vv(mom.get('plus_haut_52s')), vv(mom.get('plus_bas_52s'))
    I = {'lab': None, 'lvl': 'gris', 'mod': 0.0, 'lignes': [], 'effet': '', 'source': ini.get('source'),
         'periode': ini.get('periode') or '12 mois'}
    R['init'] = I
    if not isinstance(txs, list):
        legacy = V(G(D, 'qualite.inities'))['v']
        I['lab'] = 'NON VÉRIFIÉ'
        I['legacy'] = legacy
        warn('Initiés non vérifiés : renseigner inities.transactions (liste vide si aucune transaction trouvée) et inities.source.')
        chk('Initiés vérifiés (achats et ventes des dirigeants sur 12 mois)', 'échec',
            'champ inities absent' + (' — ancien badge : %s' % legacy if legacy else ''))
        return I
    if not ini.get('source'):
        warn('Initiés : source non nommée (registre ou publications officielles de l’émetteur).')
    a12 = v12 = a90 = 0.0
    acheteurs90, vendeurs90, acheteurs12, vendeurs12 = set(), set(), set(), set()
    pa_num = pa_den = pv_num = pv_den = 0.0
    dernier_achat = None
    for t in txs:
        if not isinstance(t, (list, tuple)) or len(t) < 6:
            warn('Transaction d’initié ignorée (format [date, nom, fonction, ACHAT|VENTE, nature, montant_eur, prix]) : %s' % (t,))
            continue
        d = _date(t[0]); nom = str(t[1] or '?'); fct = t[2]; sens = _sans_accent(str(t[3] or '')).upper()
        nature = t[4]; mt = _en_nombre(vv(t[5])) if t[5] is not None else None
        px = _en_nombre(vv(t[6])) if len(t) > 6 and t[6] is not None else None
        age = (ref - d).days if d else None
        marche = _nature_marche(nature)
        dans12 = age is not None and 0 <= age <= 365
        compte = marche and dans12 and num(mt)
        I['lignes'].append({'date': t[0], 'nom': nom, 'fonction': fct, 'sens': 'ACHAT' if 'ACHAT' in sens or 'BUY' in sens else 'VENTE',
                            'nature': nature or 'marché', 'montant': mt, 'prix': px, 'compte': bool(compte), 'age': age})
        if not compte:
            continue
        if 'ACHAT' in sens or 'BUY' in sens:
            a12 += mt; acheteurs12.add(nom)
            if num(px): pa_num += mt; pa_den += mt / px
            if age <= 90: a90 += mt; acheteurs90.add(nom)
            if dernier_achat is None or d > dernier_achat: dernier_achat = d
        else:
            v12 += mt; vendeurs12.add(nom)
            if num(px): pv_num += mt; pv_den += mt / px
            if age <= 90: vendeurs90.add(nom)
    cap_eur = capm * 1e6 if num(capm) and capm > 0 else None
    net = a12 - v12
    I.update({'a12': a12, 'v12': v12, 'a90': a90, 'net': net, 'nb_ach': len(acheteurs12), 'nb_vend': len(vendeurs12),
              'nb_ach90': len(acheteurs90), 'nb_vend90': len(vendeurs90),
              'pct_a': 100 * a12 / cap_eur if cap_eur else None, 'pct_v': 100 * v12 / cap_eur if cap_eur else None,
              'pct_net': 100 * net / cap_eur if cap_eur else None,
              'px_achat': pa_num / pa_den if pa_den else None, 'px_vente': pv_num / pv_den if pv_den else None,
              'dernier_achat': dernier_achat.strftime('%d/%m/%Y') if dernier_achat else None,
              'mois_dernier_achat': (ref - dernier_achat).days / 30.44 if dernier_achat else None})
    seuil = max(INIT_MIN_EUR, (cap_eur or 0) * INIT_FORT_PCT / 100)
    achat_fort = (net >= seuil) or (len(acheteurs90) >= INIT_CLUSTER and a90 >= INIT_MIN_EUR and v12 < a12 / 2)
    vente_forte = (-net >= seuil) or (len(vendeurs90) >= INIT_CLUSTER and v12 >= INIT_MIN_EUR and a12 < v12 / 2)
    pos = None
    if num(I['px_vente']) and num(hi) and num(lo) and hi > lo:
        pos = (I['px_vente'] - lo) / (hi - lo)
    I['pos_vente'] = pos
    I['seuil'] = seuil
    if achat_fort and vente_forte:
        I['lab'], I['lvl'] = 'SIGNAUX CONTRAIRES', 4
        I['effet'] = 'achats et ventes forts en même temps : aucun effet'
    elif achat_fort:
        I['lab'], I['lvl'], I['mod'] = 'ACHAT FORT DES INITIÉS', 6, -1.0
        I['effet'] = 'taux exigé −1 pt et tranches 50 / 25 / 25 %'
    elif vente_forte and num(pos) and pos <= INIT_BAS_TIERS:
        I['lab'], I['lvl'], I['mod'] = 'VENTES FORTES AU PLUS BAS', 2, 1.0
        I['effet'] = 'taux exigé +1 pt et tranches en tiers'
    elif vente_forte:
        I['lab'], I['lvl'] = 'VENTES FORTES', 3
        I['effet'] = 'alerte sans effet sur le prix (ventes hors du tiers bas du range 52 semaines%s)' % (
            '' if num(pos) else ' — plus haut et plus bas 52 semaines non fournis, position non mesurée')
    elif a12 > 0 and a12 >= v12:
        I['lab'], I['lvl'] = 'ACHATS LIMITÉS', 5
        I['effet'] = 'sous le seuil d’un achat fort : aucun effet'
    elif v12 > 0:
        I['lab'], I['lvl'] = 'VENTES LIMITÉES', 4
        I['effet'] = 'sous le seuil de ventes fortes : aucun effet'
    else:
        I['lab'], I['lvl'] = 'AUCUNE TRANSACTION', 4
        I['effet'] = 'aucune transaction de marché trouvée sur 12 mois : aucun effet'
    if I['mod'] < 0 and num(I.get('mois_dernier_achat')) and I['mois_dernier_achat'] > 6:
        I['effet'] += ' — dernier achat il y a %s mois : signal qui vieillit' % fr(I['mois_dernier_achat'], 0)
    chk('Initiés vérifiés (achats et ventes des dirigeants sur 12 mois)', 'validé',
        '%s · %s' % (I['lab'], ini.get('source') or 'source non nommée'))
    return I


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
    iqr, ab, nn = rb.get('iqr_eff'), rb.get('au_dessus'), rb.get('n')
    if (num(Q) and Q >= 85 and num(vis) and vis >= 70 and num(iqr) and iqr <= 5
            and num(ab) and num(nn) and nn >= 5 and ab >= 5
            and rb.get('tend') != 'EN BAISSE' and rb.get('metrique_ok', True)
            and not rb.get('serie_estimee')
            and all(((q.get('pil') or {}).get(k) or {}).get('obs') == 3 for k in ('capital', 'visibilite'))):
        mods.append(('qualit\u00e9 prouv\u00e9e (Q\u226585, visibilit\u00e9\u226570 %%, stabilit\u00e9 %s \u22645 pts, 5 ans > co\u00fbt du capital, tendance non baissi\u00e8re)' % rb.get('metrique', 'ROIC'), -2.0))

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
    if (num(Q) and Q >= 85 and not any(m[1] == -2.0 for m in mods)
            and (rb.get('serie_estimee') or not all(((q.get('pil') or {}).get(k) or {}).get('obs') == 3
                                                     for k in ('capital', 'visibilite')))):
        warn('Bonus \u00ab qualit\u00e9 prouv\u00e9e \u00bb refus\u00e9 : s\u00e9rie de rentabilit\u00e9 estim\u00e9e ou contr\u00f4le Capital/Visibilit\u00e9 non observ\u00e9.')
    if key in DROITS:
        pass
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

    ini_ = R.get('init') or {}
    if ini_.get('mod'):
        mods.append(('initi\u00e9s : %s' % ini_['lab'].lower(), ini_['mod']))

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
        warn('Taux exig\u00e9 brut %s %% > %.0f %% : le risque d\u00e9passe ce qu\'un prix peut compenser. '
             'Tout ACHAT est neutralis\u00e9 par le moteur \u2014 orientation HORS S\u00c9LECTION.' % (fr(brut, 1), TX_MAX))
        chk('Taux exig\u00e9 dans la plage 12\u201321 %%', '\u00e9chec', 'brut %.1f %%' % brut)
    elif brut < TX_MIN - 1e-9:
        warn('Taux exig\u00e9 brut %s %% < %.0f %% : plancher appliqu\u00e9.' % (fr(brut, 1), TX_MIN))
    chk('Taux exig\u00e9 calcul\u00e9 par le moteur', 'valid\u00e9',
        '%.1f %% (base 15 %%, %d modificateur(s)%s)' % (tx, len(mods), ', born\u00e9' if R['tx_borne'] else ''))
    return tx


def calc_qualite(q, wacc_absent, rb=None, rent=None):
    rb = rb or {}; rent = rent or {}
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
        if k == 'capital' and num(notes[0]):
            notes[0] = plafond_capital1(notes[0], rb, rent)
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
    out['tend'], out['pente'], out['iqr_res'], out['chute_max'] = tendance_roic(vals)
    out['iqr_eff'] = out['iqr_res'] if out['tend'] == 'EN HAUSSE' else out['iqr']
    if out['tend'] == 'EN HAUSSE' and num(out['iqr_res']) and out['iqr_res'] > 5:
        out['iqr_eff'] = out['chute_max']  # V22.9.1 : hausse monotone qui accelere
    if n < 3:
        return dict(out, lab='HISTORIQUE INSUFFISANT', lvl='gris')
    if not num(wacc):
        return dict(out, lab='CO\u00dbT DU CAPITAL NON \u00c9VALU\u00c9', lvl='gris')
    ab = sum(1 for v in vals if v > wacc)
    out['au_dessus'] = ab
    iqr = out['iqr_eff'] if out['iqr_eff'] is not None else 0
    if n >= 5 and out['med'] <= 0:
        lab, l = 'DESTRUCTION PERSISTANTE', 1
    elif out['med'] <= wacc:
        lab, l = 'SOUS LE CO\u00dbT DU CAPITAL', 2
    elif ab <= n / 2 or out['last'] <= wacc:
        lab, l = 'FRAGILE', 3
    elif ab < n or iqr > 5:
        lab, l = 'IRR\u00c9GULI\u00c8RE', 4
        i0 = next((i for i, v in enumerate(vals) if v > wacc), None)
        if (out['tend'] == 'EN HAUSSE' and iqr <= 5 and i0 is not None
                and all(v > wacc for v in vals[i0:])):
            lab = 'EN ASCENSION'  # V22.9.1 : seules les premieres annees sont sous le cout du capital
    elif n < 5:
        lab, l = 'HISTORIQUE COURT', 4
    elif out['min'] >= wacc + 3 and out['med'] >= wacc + 8:
        lab, l = 'RENTABILIT\u00c9 DURABLE EXCEPTIONNELLE', 6
    else:
        lab, l = 'RENTABLE ET STABLE', 5
    if n < 5 and isinstance(l, int) and l > 4:
        lab, l = 'HISTORIQUE COURT', 4
    if isinstance(l, int) and l >= 5 and out['tend'] == 'EN HAUSSE' and lab != 'RENTABILIT\u00c9 DURABLE EXCEPTIONNELLE':
        lab = 'RENTABILIT\u00c9 EN PROGRESSION'
    elif isinstance(l, int) and l >= 5 and out['tend'] == 'EN BAISSE':
        lab, l = 'RENTABLE MAIS EN BAISSE', 4
    return dict(out, lab=lab, lvl=l)


METRIQUES = {'ROIC': 'ROIC', 'ROCE APR\u00c8S IMP\u00d4T': 'ROCE apr\u00e8s imp\u00f4t', 'ROCE APRES IMPOT': 'ROCE apr\u00e8s imp\u00f4t',
             'ROE': 'ROE', 'ROE (SECTEUR FINANCIER)': 'ROE', 'ROTE (SECTEUR FINANCIER)': 'ROTE'}


def tendance_roic(vals):
    """Tendance mesuree par regression lineaire : pente (pts/an) et dispersion
    des residus. Une progression reguliere n'est pas une instabilite (V22.5)."""
    n = len(vals)
    if n < 4:
        return None, None, None, None
    mx, my = (n - 1) / 2.0, sum(vals) / n
    pente = sum((i - mx) * (v - my) for i, v in enumerate(vals)) / sum((i - mx) ** 2 for i in range(n))
    res = [v - (my + pente * (i - mx)) for i, v in enumerate(vals)]
    qs = stx.quantiles(res, n=4, method='inclusive')
    iqr_res = qs[2] - qs[0]
    iqr = stx.quantiles(vals, n=4, method='inclusive')
    iqr = iqr[2] - iqr[0]
    chute_max = max([0] + [vals[i - 1] - vals[i] for i in range(1, n)])
    monotone = chute_max <= 1  # V22.9.1 : aucun recul annuel de plus d'1 pt
    if pente >= 1 and vals[-1] >= vals[0] + 2 and (iqr_res <= 5 or monotone):
        t = 'EN HAUSSE'
    elif pente <= -1 and vals[-1] <= vals[0] - 2:
        t = 'EN BAISSE'
    elif iqr <= 5:
        t = 'STABLE'
    else:
        t = 'VOLATILE'
    return t, pente, iqr_res, chute_max


def completer_rentab(rb, rent):
    """Ajoute tendance, stabilite effective et metrique au badge de rentabilite."""
    lab = str(vv(rent.get('metrique')) or 'ROIC').strip().upper()
    rb['metrique'] = METRIQUES.get(lab, 'ROIC')
    rb['finance'] = 'SECTEUR FINANCIER' in lab
    if lab not in METRIQUES:
        warn('M\u00e9trique de rentabilit\u00e9 non reconnue (%s) : trait\u00e9e comme ROIC.' % lab)
    lev = vv(rent.get('levier'))
    rb['levier'] = lev
    serie = rent.get('roic') or []
    rb['serie_estimee'] = (str(vv(rent.get('prov')) or '').strip().upper().startswith('E') or any(
        isinstance(x, (list, tuple)) and len(x) > 2 and str(x[2]).strip().upper().startswith('E') for x in serie))
    rb['metrique_ok'] = True
    if rb['metrique'] == 'ROE' and not rb['finance']:
        rb['metrique_ok'] = False
        warn('Rentabilit\u00e9 mesur\u00e9e par le ROE hors secteur financier : comparabilit\u00e9 r\u00e9duite, '
             'bonus de qualit\u00e9 prouv\u00e9e du taux exig\u00e9 non applicable.')
    return rb


def plafond_capital1(note, rb, rent):
    """Capital 1 ne peut valoir 1 que si les conditions mesurables sont reunies (V22.5)."""
    motifs = []
    wacc, med, n, ab = rb.get('wacc'), rb.get('med'), rb.get('n') or 0, rb.get('au_dessus')
    if num(wacc) and num(med) and n >= 5:
        if med < wacc + 3: motifs.append('m\u00e9diane < co\u00fbt du capital + 3 pts')
        if num(ab) and ab < n: motifs.append('au moins une ann\u00e9e sous le co\u00fbt du capital')
        if num(rb.get('iqr_eff')) and rb['iqr_eff'] > 5: motifs.append('stabilit\u00e9 > 5 pts (tendance comprise)')
    elif n < 5:
        motifs.append('historique < 5 ans')
    if rb.get('tend') == 'EN BAISSE' and not (rent.get('baisse_expliquee') and rent.get('tendance_preuve')):
        motifs.append('rentabilit\u00e9 en baisse sans mont\u00e9e en puissance document\u00e9e')
    lev = rb.get('levier')
    if rb.get('metrique') == 'ROE' and not rb.get('finance') and (not num(lev) or lev > 0.5):
        motifs.append('ROE hors finance avec levier %s' % ('non renseign\u00e9' if not num(lev) else '> 0,5'))
    if note > 0.5 and motifs:
        warn('Capital 1 plafonn\u00e9 \u00e0 0,5 par le moteur : ' + ' ; '.join(motifs) + '.')
        return 0.5
    if note == 0.5 and not motifs and rb.get('tend') == 'EN HAUSSE' and num(med) and num(wacc) and n >= 5:
        warn('Capital 1 not\u00e9 0,5 alors que la progression r\u00e9guli\u00e8re remplit les conditions de 1 : '
             'v\u00e9rifier la notation (ancien test IQR p\u00e9nalisant une hausse).')
    return note


def barC(x):
    if not num(x):
        return None
    return 100 if x >= 15 else 80 if x >= 10 else 60 if x >= 6 else 35 if x >= 3 else 10 if x >= 0 else 0


# ------------------------------------------------------------------ moteur financier
TK_DEF = [0.0, 1.0, 2.0, 3.0, 4.0]


def bpa_at(sc, base, t, gt, tk=None):
    """BPA des 12 mois glissants a la date t (annees depuis l'evaluation). tk = dates des clotures
    [base, ex.1 .. ex.4] ; interpolation geometrique entre deux clotures, extrapolation prudente au-dela (V22.6)."""
    tk = tk or TK_DEF
    b = [base if num(base) else sc['bpa'][0]] + list(sc['bpa'])
    if t <= tk[0]:
        return b[0]
    if t <= tk[4] + 1e-12:
        for i in range(4):
            if tk[i] - 1e-12 <= t <= tk[i + 1] + 1e-12:
                f = (t - tk[i]) / (tk[i + 1] - tk[i])
                a, c = b[i], b[i + 1]
                if f <= 1e-12:
                    return a
                if f >= 1 - 1e-12:
                    return c
                return a * (c / a) ** f if (a > 0 and c > 0) else a + (c - a) * f
    return b[4] * (1 + gt / 100.0) ** (t - tk[4])


def dps_at(sc, k, gt):
    d = sc.get('dps') or [0, 0, 0, 0]
    return d[k - 1] if k <= 4 else d[3] * (1 + gt / 100.0) ** (k - 4)


def fx_at(sc, x0, t):
    f = sc.get('fx')
    if not f:
        return x0
    return f[min(max(int(math.ceil(t)), 1), 4) - 1]


def tn_sc(sc, ctx):
    """V22.7.1 : tresorerie nette et produit financier net par action a l'horizon, pour ce scenario."""
    tn = sc.get('tresorerie_an4') if num(sc.get('tresorerie_an4')) else ctx.get('tn')
    pf = sc.get('produit_fin_an4') if num(sc.get('produit_fin_an4')) else ctx.get('pf')
    return (tn if num(tn) else 0.0), (pf if num(pf) else 0.0)


def val_term(sc, ctx, h=4.0, mult=None):
    """Valeur par action a l'horizon : exploitation x multiple + tresorerie nette (V22.7.1)."""
    m = sc['multiple'] if mult is None else mult
    tn, pf = tn_sc(sc, ctx)
    expl = bpa_at(sc, ctx['base'], h, ctx['gt'], ctx.get('tk')) - pf
    return max(0.0, max(0.0, expl) * m + tn)


def flux(P, sc, ctx, h=4.0, mult=None, divs=True):
    x0 = ctx['x0']; B = P * x0
    I0 = B * (1 + TOB + ctx['fa'])
    cf = {0.0: -I0}
    if divs:
        tk, dl = ctx.get('tk') or TK_DEF, ctx.get('delai', 0.0)
        k = 1
        while True:
            tp = (tk[k] if k <= 4 else tk[4] + (k - 4)) + dl
            if tp > h + 1e-9:
                break
            if tp > 1e-9:  # dividende deja paye a la date d'evaluation : exclu
                tq = round(tp, 6)
                cf[tq] = cf.get(tq, 0.0) + dps_at(sc, k, ctx['gt']) * fx_at(sc, x0, tp) * ctx['net_div']
            k += 1
    S = val_term(sc, ctx, h, mult) * fx_at(sc, x0, h)
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
                 'rentabilite.wacc', 'plancher.tresorerie_nette_meur',
                 'valo.tresorerie_nette_action', 'valo.produit_financier_action',
                 'risques.forensique.z_altman', 'risques.forensique.o_ohlson_pct',
                 'risques.forensique.m_beneish', 'risques.forensique.f_piotroski',
                 # V23
                 'risques.forensique.sloan', 'profil.etat_pct',
                 'creation_valeur.spread', 'creation_valeur.spread_5a', 'creation_valeur.spread_pire_10a',
                 'creation_valeur.eva_marge', 'creation_valeur.eva_momentum']
CHAMPS_NUM_VV += [f'{bloc}.{champ}' for bloc in ('autofinancement', 'triangle') for champ in (
    'reinvestissement', 'rendement_marginal', 'roe', 'variation_actions', 'croissance_comparable')]
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
        v = float(t)
        if not math.isfinite(v):
            raise ValueError(x)  # V23.2 : 'inf' ou 'nan' illisibles
        return v
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
        if isinstance(brut, list) and not brut:  # V23.2 : liste vide = n.d., jamais un plantage
            parent[cle] = None
            notes.append('%s : liste vide \u2014 n.d.' % path)
            return
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

    if isinstance(D.get('valo'), dict) and 'scenarios' in D['valo'] and not isinstance(D['valo']['scenarios'], dict):
        notes.append('valo.scenarios illisible (pas un objet) \u2014 trait\u00e9 comme absent, arr\u00eat pr\u00e9coce.')
        D['valo']['scenarios'] = {}
    scs = G(D, 'valo.scenarios') or {}
    for nom, sc in (scs.items() if isinstance(scs, dict) else []):
        if not isinstance(sc, dict):
            continue
        for k in ('multiple', 'poids', 'tresorerie_an4', 'produit_fin_an4'):
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


def _date(x):
    x = str(vv(x) or '').strip()
    for f in ('%d/%m/%Y', '%Y-%m-%d', '%d-%m-%Y', '%d.%m.%Y'):
        try:
            return datetime.datetime.strptime(x, f).date()
        except ValueError:
            pass
    if re.fullmatch(r'\d{4}', x):
        return datetime.date(int(x), 12, 31)
    return None


def _plus_ans(d, n):
    try:
        return d.replace(year=d.year + n)
    except ValueError:
        return d.replace(year=d.year + n, day=28)


def aligner_exercices(D, R):
    """V22.6 : place les clotures des exercices projetes sur l'axe du temps de l'evaluation.
    Convention : la base normalisee est celle du dernier exercice clos avant le premier exercice projete ;
    le BPA de sortie est celui des 12 mois glissants a la date d'evaluation + 4 ans ; le dividende de
    l'exercice k est verse a sa cloture + delai (4 mois par defaut)."""
    meta = D.get('meta') or {}; valo = D.get('valo') or {}
    ev = _date(meta.get('date_eval')) or _date(meta.get('date_cours'))
    c1 = _date(valo.get('premier_exercice'))
    R['alignement'] = None
    if not (ev and c1):
        warn('Exercices non align\u00e9s : renseigner valo.premier_exercice (date de cl\u00f4ture du premier exercice projet\u00e9). '
             'Convention par d\u00e9faut : exercices r\u00e9put\u00e9s clos aux anniversaires de l\u2019\u00e9valuation.')
        chk('Alignement des exercices sur la date de sortie', '\u00e9chec' if ev else 'n.d.',
            'premier_exercice absent' if ev else 'date d\u2019\u00e9valuation illisible')
        return TK_DEF, 0.0
    tk = [(_plus_ans(c1, k - 1) - ev).days / 365.25 for k in range(0, 5)]
    dm = valo.get('delai_dividende_mois')
    dm = vv(dm) if num(vv(dm)) else 4
    sortie = _plus_ans(ev, 4)
    R['alignement'] = {'clotures': [_plus_ans(c1, k - 1).strftime('%d/%m/%Y') for k in range(0, 5)],
                       'sortie': sortie.strftime('%d/%m/%Y'), 'tk': tk, 'delai_mois': dm}
    ok = True
    if tk[1] > 1.05:
        ok = False
        warn('Premier exercice projet\u00e9 clos %s mois apr\u00e8s l\u2019\u00e9valuation : l\u2019exercice en cours manque.' % fr(tk[1] * 12, 0))
    if tk[1] < -0.5:
        ok = False
        warn('Premier exercice projet\u00e9 d\u00e9j\u00e0 clos depuis plus de six mois : il appartient \u00e0 l\u2019historique, d\u00e9caler d\u2019un an.')
    ext = 4 - tk[4]
    R['alignement']['extrapolation_mois'] = max(0.0, ext * 12)
    if ext > 1.0 + 1e-9:
        warn('Sortie %s mois apr\u00e8s la derni\u00e8re cl\u00f4ture projet\u00e9e : BPA extrapol\u00e9 \u00e0 la croissance terminale prudente. '
             'Projeter plut\u00f4t un exercice plus loin.' % fr(ext * 12, 0))
    chk('Alignement des exercices sur la date de sortie', 'valid\u00e9' if ok else '\u00e9chec',
        'cl\u00f4tures %s \u2192 %s ; sortie le %s ; BPA de sortie = 12 mois glissants%s ; dividendes vers\u00e9s \u00e0 cl\u00f4ture + %s mois'
        % (R['alignement']['clotures'][1], R['alignement']['clotures'][4], R['alignement']['sortie'],
           (' (dont %s mois prolong\u00e9s au rythme prudent de la derni\u00e8re ann\u00e9e)' % fr(ext * 12, 0)) if ext > 0.02 else ' interpol\u00e9s',
           fr(dm, 0)))
    return tk, dm / 12.0



# ------------------------------------------------------------------ V22.7 : plancher de perte
ANCRAGES = ('PIRE EXERCICE', 'CHOC CHIFFR', 'MILIEU DE CYCLE', 'TEST DEMANDE')


def eval_baissier(D, R, scs):
    """Credibilite du baissier : un baissier trop gentil ne peut ni baisser le taux, ni grossir la ligne.
    CREDIBLE = ancre sur un fait, nettement sous le central, solvabilite mesuree et saine, pas d'alerte comptable.
    DOUTEUX = un test echoue. NON VERIFIE = rien d'anormal mais mesure de solvabilite absente."""
    Bs, Cc = scs.get('baissier') or {}, scs.get('central') or {}
    fo = G(D, 'risques.forensique')
    fo = fo if isinstance(fo, dict) else {}  # V23.2 : champ malforme = n.d., jamais un plantage
    z, o = vv(fo.get('z_altman')), vv(fo.get('o_ohlson_pct'))
    m, f = vv(fo.get('m_beneish')), vv(fo.get('f_piotroski'))
    financier = est_financier(D)  # V23.3 : qualification explicite, plus de detection par le nom du secteur
    tests = []  # (libelle, etat True/False/None, detail)
    anc = Bs.get('ancrage')
    lab = str((anc[0] if isinstance(anc, list) and anc else anc) or '').strip().upper()
    fait = str((anc[1] if isinstance(anc, list) and len(anc) > 1 else '') or '').strip()
    ok_anc = bool(lab) and any(a in _sans_accent(lab).upper() or a in lab for a in ANCRAGES) and bool(fait)
    if not anc:
        warn('Ancrage du baissier non renseign\u00e9 (valo.scenarios.baissier.ancrage) : baissier NON V\u00c9RIFI\u00c9, aucun bonus de plancher.')
    tests.append(('Ancrage du baissier', ok_anc if anc else None,
                  ('%s : %s' % (lab, fait)) if ok_anc else 'absent ou sans fait (PIRE EXERCICE, CHOC CHIFFRÉ, MILIEU DE CYCLE, TEST DEMANDE −20 %)'))
    rt = None
    try:
        cx = R.get('ctx') or {'base': None, 'gt': 0.0}
        vb = val_term(Bs, cx) if 'base' in cx else Bs['bpa'][3] * Bs['multiple']
        vc = val_term(Cc, cx) if 'base' in cx else Cc['bpa'][3] * Cc['multiple']
        rt = vb / vc * 100 if vc > 0 else None
    except (KeyError, TypeError, IndexError):
        pass
    tests.append(('Écart au central', None if rt is None else rt < 80,
                  'valeur terminale baissière = %s %% de la centrale (il faut < 80 %%)' % fr(rt, 0) if num(rt) else 'n.d.'))
    if financier:
        tests.append(('Solvabilité (Altman / Ohlson)', None, 'non applicable au secteur financier'))
        solv = True
    elif num(z) or num(o):
        det = (num(z) and z < 1.81) or (num(o) and o >= 50)
        solv = not det
        tests.append(('Solvabilité (Altman / Ohlson)', solv,
                      'Z %s%s · O %s%s' % (fr(z, 2), ' (zone de détresse <1,81)' if num(z) and z < 1.81 else
                                           ' (zone grise)' if num(z) and z < 2.99 else '',
                                           (fr(o, 0) + ' %') if num(o) else 'n.d.', ' (≥50 % : défaut probable)' if num(o) and o >= 50 else '')))
    else:
        solv = None
        tests.append(('Solvabilité (Altman / Ohlson)', None, 'non mesurée — à reprendre dans Unclestock'))
    if num(m):
        tests.append(('Comptes (Beneish M)', m <= -1.78, 'M %s%s' % (fr(m, 2), ' > −1,78 : manipulation possible' if m > -1.78 else '')))
    else:
        tests.append(('Comptes (Beneish M)', None, 'non calculé (métrique éparse : absence non pénalisée)'))
    if num(f):
        tests.append(('Solidité (Piotroski F)', None if f > 3 else False, 'F %s/9%s' % (fr(f, 0), ' : faiblesse' if f <= 3 else '')))
    echec = [t for t in tests if t[1] is False]
    if echec:
        lab_b = 'DOUTEUX'
    elif ok_anc and num(rt) and solv is not None:
        lab_b = 'CRÉDIBLE'
    else:
        lab_b = 'NON VÉRIFIÉ'
    R['baissier'] = {'lab': lab_b, 'tests': tests, 'ratio_central': rt,
                     'lvl': {'CRÉDIBLE': 5, 'DOUTEUX': 2}.get(lab_b, 'gris')}
    chk('Baissier crédible (V22.7)', {'CRÉDIBLE': 'validé', 'DOUTEUX': 'échec'}.get(lab_b, 'n.d.'),
        ' ; '.join('%s : %s' % (t[0], t[2]) for t in tests if t[1] is not True) or 'tous les tests passés')
    if lab_b == 'DOUTEUX':
        warn('Baissier DOUTEUX (%s) : capital préservé possiblement surestimé ; ni modificateur plancher, ni bonus de taille, taille plafonnée à 3 %%.'
             % ' ; '.join(t[0] for t in echec))
    return lab_b


def prix_plancher(Bs, ctx, pmax, cible=CAP_MIN):
    """Prix le plus haut qui garde le capital preserve du baissier >= cible (regle des -40 %)."""
    cap = lambda P: cap_preserve(P, Bs, ctx)
    lo, hi = pmax * 1e-6, pmax
    try:
        if cap(hi) >= cible:
            return hi
        if cap(lo) < cible:
            return None
    except (ZeroDivisionError, ValueError, TypeError):
        return None
    for _ in range(80):
        mid = (lo + hi) / 2
        if cap(mid) >= cible:
            lo = mid
        else:
            hi = mid
    return lo


def poser_prix(R, tx, _prix, prix_pour, flux, C, ctx, pmax, mact):
    R['tx_bandes'] = (tx, max(2.0, tx - 5), max(2.0, tx - 10))
    R['PA'] = _prix(tx / 100.0)
    R['PJ'] = _prix(R['tx_bandes'][1] / 100.0)
    R['PO'] = _prix(R['tx_bandes'][2] / 100.0)
    R['PR'] = _prix(min(0.30, (tx + 3) / 100.0))
    R['PS'] = _prix(min(0.30, (tx + 6) / 100.0))
    R['tx_action'] = (tx, min(30.0, tx + 3), min(30.0, tx + 6))
    R['PA_sans_revalo'] = prix_pour(tx / 100.0, lambda P: flux(P, C, ctx, 4, mact)[0], pmax) if num(mact) else None


def appliquer_plancher(D, R, Bs, ctx, pmax, _prix, C, mact):
    """A : le prix d'achat ne peut pas depasser le prix plancher (-40 % au pire dans le baissier).
    B : plancher prouve -> taux exige -1 pt si toutes les conditions factuelles sont reunies."""
    R['P60'] = prix_plancher(Bs, ctx, pmax)
    # ---- B : plancher prouve
    meta = D.get('meta') or {}
    pl = D.get('plancher') or {}
    tn, capm = vv(pl.get('tresorerie_nette_meur')), vv(meta.get('capitalisation_meur'))
    dis = pl.get('distribution')
    dlab = str((dis[0] if isinstance(dis, list) and dis else dis) or '').strip().upper()
    dtxt = str((dis[1] if isinstance(dis, list) and len(dis) > 1 else '') or '').strip()
    cond = [('trésorerie nette ≥ 20 % de la capitalisation',
             bool(num(tn) and num(capm) and capm > 0 and tn / capm * 100 >= CASH_B),
             ('%s %%' % fr(tn / capm * 100, 0)) if (num(tn) and num(capm) and capm > 0) else 'n.d.'),
            ('cash réellement distribué sur 3 ans', dlab.startswith('OUI') and bool(dtxt), dtxt or 'n.d.'),
            ('baissier crédible', (R.get('baissier') or {}).get('lab') == 'CRÉDIBLE', (R.get('baissier') or {}).get('lab', 'n.d.')),
            ('porte qualité franchie', bool(R['q'].get('porte')), 'Q %s %%' % fr(R['q'].get('Q'), 0))]
    R['B_cond'] = cond
    R['B_actif'] = False
    tx = R['tx']
    if all(c[1] for c in cond):
        brut2 = R['tx_brut'] - 1.0
        tx2 = max(TX_MIN, min(TX_MAX, round(brut2 * 2) / 2))
        if tx2 < tx - 1e-9:
            pa2 = _prix(tx2 / 100.0)
            pa2e = min(pa2, R['P60']) if (num(pa2) and num(R['P60'])) else pa2
            cap2 = cap_preserve(pa2e, Bs, ctx) if num(pa2e) else None
            cond.append(('capital préservé ≥ 80 au nouveau prix d’achat', bool(num(cap2) and cap2 >= CAP_B),
                         '%s /100' % fr(cap2, 0)))
            if num(cap2) and cap2 >= CAP_B:
                R['tx_mods'].append(('plancher prouvé (trésorerie nette, cash distribué, baissier crédible, capital ≥ 80 au prix d’achat)', -1.0))
                R['tx_brut'], R['tx'], R['B_actif'] = brut2, tx2, True
                R['tx_borne'] = abs(brut2 - tx2) > 1e-9
                chk('Modificateur plancher prouvé', 'validé', 'taux exigé %s → %s %%' % (fr(tx, 1), fr(tx2, 1)))
        else:
            cond.append(('effet sur le taux', False, 'taux déjà au plancher de 12 %'))
    if not R['B_actif']:
        chk('Modificateur plancher prouvé', 'n.a.', ' ; '.join('%s : %s' % (c[0], c[2]) for c in cond if not c[1]) or 'sans effet')
    poser_prix(R, R['tx'], _prix, prix_pour, flux, C, ctx, pmax, mact)
    # ---- A : regle des -40 %
    R['PA_fond'] = R['PA']
    R['plancher_limite'] = False
    if R['P60'] is None:
        R['plancher_limite'] = True
        for k in ('PA', 'PR', 'PS'):
            R[k] = None
        warn('Aucun prix ne garde 60/100 dans le baissier : la règle des −40 %% bloque tout prix d’achat.')
        chk('Règle des −40 % (capital préservé ≥ 60)', 'échec', 'aucun prix admissible')
        return
    if num(R['PA']) and R['P60'] < R['PA'] - 1e-9:
        R['plancher_limite'] = True
        for k in ('PA', 'PR', 'PS'):
            if num(R[k]):
                R[k] = min(R[k], R['P60'])
        warn('Prix d’achat ramené de %s à %s par la règle des −40 %% (capital préservé du baissier ≥ 60/100).'
             % (fprix(R['PA_fond']), fprix(R['PA'])))
    chk('Règle des −40 % (capital préservé ≥ 60)', 'validé',
        'prix plancher %s%s' % (fprix(R['P60']), ' — limite le prix d’achat' if R['plancher_limite'] else ' — non contraignant'))


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
    R['rentab'] = completer_rentab(roic_badge(rent.get('roic'), vv(rent.get('wacc'))), rent)
    R['q'] = calc_qualite(D.get('qualite') or {}, not num(vv(rent.get('wacc'))), R['rentab'], rent)
    decl = str(vv(rent.get('tendance')) or '').upper()
    if R['rentab'].get('tend') and decl in ('STABLE', 'EN HAUSSE', 'EN BAISSE', 'VOLATILE') and decl != R['rentab']['tend']:
        warn('Tendance de rentabilit\u00e9 d\u00e9clar\u00e9e %s, mesur\u00e9e %s : expliquer l\u2019\u00e9cart dans tendance_preuve.' % (decl, R['rentab']['tend']))
    calc_inities(D, R)
    calc_taux_exige(D, R)

    scs = valo.get('scenarios') or {}
    base = vv(valo.get('base_normalisee'))
    gc = G(D, 'croissance.g_centrale')
    if not isinstance(scs, dict):
        scs = {}
    _c = scs.get('central')
    gc_calc = None
    if (isinstance(_c, dict) and isinstance(_c.get('bpa'), list) and len(_c['bpa']) == 4
            and num(_c['bpa'][3]) and num(base) and base > 0 and _c['bpa'][3] > 0):
        gc_calc = 100 * ((_c['bpa'][3] / base) ** 0.25 - 1)
    R['gc_declaree'] = gc
    if num(gc_calc):
        if num(gc) and abs(gc - gc_calc) > 1 + 1e-9:
            warn('Croissance centrale d\u00e9clar\u00e9e %s %%/an, calcul\u00e9e depuis les sc\u00e9narios %s %%/an : '
                 'le moteur retient la valeur calcul\u00e9e.' % (fr(gc, 1), fr(gc_calc, 1)))
            chk('Croissance centrale coh\u00e9rente avec les sc\u00e9narios', '\u00e9chec',
                '\u00e9cart %s pt' % fr(gc - gc_calc, 1, True))
        else:
            chk('Croissance centrale coh\u00e9rente avec les sc\u00e9narios', 'valid\u00e9',
                'BPA de la base au 4e exercice : %s %%/an' % fr(gc_calc, 1))
        gc = gc_calc
    elif num(gc):
        warn('Croissance centrale non recalculable (base n\u00e9gative, nulle ou absente) : valeur d\u00e9clar\u00e9e utilis\u00e9e.')
    go = G(D, 'croissance.g_organique_hist')
    R['gc'], R['go'] = gc, go
    bo, bg = barC(go), barC(gc)
    R['C'] = None if (bo is None or bg is None) else 0.5 * bo + 0.5 * bg

    def _sc_ok(sc):  # V22.4.1 : un scenario incomplet vaut arret precoce, jamais un plantage
        return (isinstance(sc, dict) and isinstance(sc.get('bpa'), list) and len(sc['bpa']) == 4
                and all(num(x) for x in sc['bpa']) and num(sc.get('multiple')))
    if not (num(cours) and cours > 0 and all(_sc_ok(scs.get(k)) for k in ('baissier', 'central', 'haussier'))):
        chk('Calculs financiers', 'n.a.', 'scénarios incomplets ou cours absent/non positif — arrêt précoce')
        lire_preuves(D, R)
        verdict_final(D, R)
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
    tk, delai = aligner_exercices(D, R)
    ctx = {'x0': x0, 'base': base, 'gt': gt, 'tk': tk, 'delai': delai,
           'fa': (valo.get('frais_achat_pct') or 0) / 100.0,
           'fv': (valo.get('frais_vente_pct') or 0) / 100.0,
           'net_div': (1 - (valo.get('retenue_etrangere') or 0)) * (1 - (valo.get('precompte', 0.30) or 0)),
           'tn': vv(valo.get('tresorerie_nette_action')), 'pf': vv(valo.get('produit_financier_action'))}
    R['ctx'] = ctx
    tn0 = ctx['tn']
    tnm, capm = vv(G(D, 'plancher.tresorerie_nette_meur')), vv(G(D, 'meta.capitalisation_meur'))
    if num(tn0):
        if not num(ctx['pf']):
            warn('Tr\u00e9sorerie nette s\u00e9par\u00e9e mais produit financier net par action absent : '
                 'les int\u00e9r\u00eats restent dans le BPA multipli\u00e9, le cash est compt\u00e9 deux fois en partie.')
        chk('Tr\u00e9sorerie nette compt\u00e9e hors multiple (V22.7.1)', 'valid\u00e9' if num(ctx['pf']) else '\u00e9chec',
            'valeur de sortie = (BPA \u2212 %s) \u00d7 multiple + %s par action ; multiples de r\u00e9f\u00e9rence \u00e0 exprimer hors cash'
            % (fr(ctx['pf'], 2), fr(tn0, 2)))
    elif num(tnm) and num(capm) and capm > 0 and tnm >= 0.10 * capm:
        warn('Tr\u00e9sorerie nette = %s %% de la capitalisation, non s\u00e9par\u00e9e du multiple '
             '(valo.tresorerie_nette_action) : plancher et prix d\u2019achat sous-estim\u00e9s.' % fr(100 * tnm / capm, 0))
        chk('Tr\u00e9sorerie nette compt\u00e9e hors multiple (V22.7.1)', '\u00e9chec',
            'cash net \u2265 10 %% de la capitalisation, non renseign\u00e9 par action')
    C, Bs = scs['central'], scs['baissier']
    R['_Bs'] = Bs  # V25.1 : lecture seule (zone d'entree Voie B, pile / face au prix d'entree)
    eval_baissier(D, R, scs)

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
    appliquer_plancher(D, R, Bs, ctx, pmax, _prix, C, mact)
    tx = R.get('tx') or 15.0
    R['niv_retenu'] = L_RDT_TX(R['retenu'], tx)
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

    if num(tn0) and tn0 > 0 and num(R.get('PA')):
        pa_ok = R['PA'] >= tn0 - 1e-9
        chk('Prix d\u2019achat \u2265 tr\u00e9sorerie nette par action (V22.7.1)', 'valid\u00e9' if pa_ok else '\u00e9chec',
            'prix %s, tr\u00e9sorerie nette %s' % (fprix(R['PA']), fprix(tn0)))
        if not pa_ok:
            warn('Prix d\u2019achat sous la tr\u00e9sorerie nette par action : v\u00e9rifier que le cash n\u2019est ni '
                 'perdu dans le multiple, ni consid\u00e9r\u00e9 comme inaccessible sans le dire (tresorerie_an4).')
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
    ctx_e = dict(ctx)
    if not any(isinstance(scs[k], dict) and scs[k].get('fx') for k in scs):
        ctx_e.pop('x0', None)  # V22.5.1 : le prix limite en devise de cotation ne depend pas du change du jour
    empreinte = {'base': base, 'scenarios': scs, 'contexte': ctx_e, 'taux': R['tx'],
                 'ancrage': ancrage, 'tob': TOB, 'tax_pv': TAX_PV,
                 'date_eval': meta.get('date_eval'), 'version': VERSION_VALORISATION}
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
    blab = (R.get('baissier') or {}).get('lab')
    cc_ = R.get('cap_cours')
    R['forteresse'] = bool(num(cc_) and cc_ >= CAP_FORT and blab == 'CR\u00c9DIBLE')
    if num(Q) and Q >= 70:
        capQ = 6 if Q >= 90 else 5 if Q >= 85 else 4 if Q >= 80 else 3
        if R['forteresse']:
            capQ += 1  # V22.7 : plancher forteresse (>= 85/100 au cours, baissier credible)
        fac = {'A': 1, 'B': 1, 'C': 0.7, 'D': 0}.get(fiab, 1)
        if pari:
            fac = min(fac, 0.7)
        lim.append(('qualit\u00e9 ajust\u00e9e' + (' + forteresse' if R['forteresse'] else ''), capQ * fac))
    vis = R['q']['vis']
    if num(vis) and vis < 50:
        lim.append(('visibilit\u00e9 <50 %', 2))
    L = max(0.0, 1 - R['cap_cours'] / 100) if num(R['cap_cours']) else None
    if num(L) and L > 0:
        lim.append(('budget de perte 1,5 %', 1.5 / L))
    if num(cc_) and CAP_MIN <= cc_ < CAP_SOLIDE:
        lim.append(('plancher fragile (60\u201369/100)', 3))
    if blab == 'DOUTEUX':
        lim.append(('baissier douteux', 3))
    liq = meta.get('liquidite_max_pct')
    if num(liq):
        lim.append(('liquidit\u00e9', liq))
    R['taille'] = {'limites': lim, 'max': min([v for _, v in lim]) if lim else None,
                   'contrainte': min(lim, key=lambda t: t[1])[0] if lim else None,
                   'provisoire': not num(liq)}
    R['tranches'] = '50 / 25 / 25 %' if (R['momentum'] == 'FAVORABLE' and fiab != 'C' and not pari) else '1/3 \u2013 1/3 \u2013 1/3'
    _il = (R.get('init') or {}).get('lab')
    if _il == 'ACHAT FORT DES INITI\u00c9S' and fiab != 'C' and not pari:
        R['tranches'] = '50 / 25 / 25 %'
    elif _il == 'VENTES FORTES AU PLUS BAS':
        R['tranches'] = '1/3 \u2013 1/3 \u2013 1/3'
    R['tranche1'] = 'au prix admissible (≤ prix maximum d’achat) ; exposition au multiple à examiner séparément'
    # V22.7 : quand la regle des -40 % limite le prix, PROCHE = a moins de 5 points de capital preserve du seuil (55/100)
    R['PJ_eff'] = R.get('PJ')
    if R.get('plancher_limite') and num(R.get('PJ')):
        p55 = prix_plancher(Bs, ctx, pmax, CAP_MIN - 5)
        R['PJ_eff'] = min(R['PJ'], p55) if num(p55) else None
    pj = R['PJ_eff']
    R['priorite'] = ('ACTIF' if cours <= pj else 'VEILLE') if num(pj) and pj > 0 else 'non \u00e9valu\u00e9e'
    R['porte_prix'] = 'ouverte' if (num(R.get('PA')) and cours <= R['PA']) else ('PROCHE' if (num(pj) and cours <= pj) else 'LOIN')

    R['calc'] = True
    lire_preuves(D, R)
    controle_unites(D, R)
    verdict_final(D, R)
    ach = (G(D, 'verdict.achat') or '').upper()
    if 'ACHAT' in ach and 'BLOQU' not in ach and R['porte_prix'] != 'ouverte':
        chk('Coh\u00e9rence verdict / porte prix', '\u00e9chec', 'ACHAT au-dessus du prix d\'achat')
    else:
        chk('Coh\u00e9rence verdict / porte prix', 'valid\u00e9')
    if num(R['part_mult']) and R['part_mult'] > 50 and ach.startswith('ACHAT'):
        warn('Part du multiple >50 % : pari de revalorisation, pas d\'ACHAT standard.')
    # 7. taille : actionnable seulement si l'achat est admissible
    vfu = R['verdict_final'].upper()
    if any(k in vfu for k in ('REJET', 'HORS S\u00c9LECTION', 'HORS P\u00c9RIM\u00c8TRE', '\u00c0 DOCUMENTER', 'GUIDANCE')):
        R['taille']['statut'] = 'sans objet'
    elif 'WATCHLIST' in vfu:
        R['taille']['statut'] = 'conditionnel'
    else:
        R['taille']['statut'] = 'actionnable'
    chk('TRI, prix et capital pr\u00e9serv\u00e9 calcul\u00e9s par le moteur', 'valid\u00e9')
    R['calc'] = True
    return R


# ------------------------------------------------------------------ V22.6 : preuves, guidance, unites, portes
TYPES_CONF = {'OP\u00c9RATIONNEL': 'OP', 'OPERATIONNEL': 'OP', 'CHIFFRES': 'OP', 'PERSISTANCE': 'PE'}


def lire_preuves(D, R):
    res = D.get('resultats') or {}
    if 'confirmations' not in res:
        R['preuves_ok'], R['preuves_motif'] = None, 'confirmations non renseign\u00e9es'
        chk('Deux confirmations ind\u00e9pendantes', 'n.d.', R['preuves_motif'])
        g = ' '.join(str(vv(res.get(k)) or '') for k in ('guidance_cas', 'verdict')).upper()
        R['guidance_cas'] = ('IMPACT NON BORNABLE' if 'NON BORNABLE' in g else 'VETO ACTIF' if 'VETO' in g
                             else 'ALERTE MOD\u00c9LIS\u00c9E' if 'ALERTE' in g else None)
        return
    cf = [c for c in (res.get('confirmations') or []) if c]
    types, non_typees = set(), 0
    for c in cf:
        if isinstance(c, list) and c:
            t = str(c[0]).strip().upper()
            hit = [v for k, v in TYPES_CONF.items() if k in t]
            if hit:
                types.add(hit[0])
            else:
                non_typees += 1
        else:
            non_typees += 1
    if len(cf) < 2:
        R['preuves_ok'], R['preuves_motif'] = False, 'moins de deux confirmations'
    elif types >= {'OP', 'PE'}:
        R['preuves_ok'], R['preuves_motif'] = True, ''
    elif non_typees == len(cf):
        R['preuves_ok'], R['preuves_motif'] = True, ''
        warn('Confirmations non typ\u00e9es : \u00e9crire [OP\u00c9RATIONNEL ou PERSISTANCE, fait, date] pour que le moteur v\u00e9rifie '
             'qu\u2019il s\u2019agit de deux preuves de nature diff\u00e9rente.')
    else:
        R['preuves_ok'] = False
        R['preuves_motif'] = 'deux confirmations de m\u00eame nature (il faut une preuve op\u00e9rationnelle et une preuve de persistance)'
    chk('Deux confirmations ind\u00e9pendantes', 'valid\u00e9' if R['preuves_ok'] else '\u00e9chec', R['preuves_motif'])
    g = ' '.join(str(vv(res.get(k)) or '') for k in ('guidance_cas', 'verdict')).upper()
    R['guidance_cas'] = ('IMPACT NON BORNABLE' if 'NON BORNABLE' in g else 'VETO ACTIF' if 'VETO' in g
                         else 'ALERTE MOD\u00c9LIS\u00c9E' if 'ALERTE' in g else None)


def controle_unites(D, R):
    """Detecte les erreurs grossieres d'unite (pence/livres, milliers, devise) : ecart d'un facteur >=20."""
    meta = D.get('meta') or {}; valo = D.get('valo') or {}
    cours, base, mact = vv(meta.get('cours')), vv(valo.get('base_normalisee')), valo.get('multiple_actuel')
    sc = (valo.get('scenarios') or {}).get('central') or {}
    motifs = []
    if num(cours) and cours > 0 and num(base) and base > 0 and num(mact) and mact > 0:
        r = (cours / base) / mact
        if r >= 20 or r <= 0.05:
            motifs.append('cours/BPA = %s contre multiple actuel %s' % (fr(cours / base, 1), fr(mact, 1)))
    if num(cours) and cours > 0 and isinstance(sc.get('bpa'), list) and len(sc['bpa']) == 4 and num(sc['bpa'][3]) \
            and num(sc.get('multiple')) and sc['bpa'][3] > 0:
        r = sc['bpa'][3] * sc['multiple'] / cours
        if r >= 20 or r <= 0.05:
            motifs.append('valeur centrale \u00e0 4 ans = %s \u00d7 le cours' % fr(r, 2))
    dev = str(meta.get('devise') or '')
    if dev in ('GBX', 'GBp', 'GBp.', 'pence', 'ZAc', 'ILA'):
        motifs.append('cours en sous-unit\u00e9 (%s) : v\u00e9rifier que BPA et dividendes sont dans la m\u00eame unit\u00e9' % dev) if not motifs else None
    R['unites_suspectes'] = ' ; '.join(m for m in motifs if 'sous-unit' not in m) or None
    if R['unites_suspectes']:
        warn('Unit\u00e9s suspectes : ' + R['unites_suspectes'] + ' \u2014 pence/livres, milliers ou devise ?')
    elif motifs:
        warn(motifs[0])
    chk('Coh\u00e9rence des unit\u00e9s (cours, BPA, multiple)', '\u00e9chec' if R['unites_suspectes'] else 'valid\u00e9',
        R['unites_suspectes'] or '')


def portes(D, R):
    """Bandeau des portes : etat lisible de chaque condition d'achat."""
    q = R.get('q') or {}
    calc = R.get('calc')
    P = [('Qualit\u00e9', None if q.get('Q') is None else bool(q.get('porte'))),
         ('Croissance', (R['gc'] >= 5) if num(R.get('gc')) else None),
         ('Preuves', R.get('preuves_ok')),
         ('Guidance', None if R.get('guidance_cas') is None and not (D.get('resultats') or {}).get('verdict')
          else R.get('guidance_cas') not in ('VETO ACTIF', 'IMPACT NON BORNABLE')),
         ('Ancrage', bool(R.get('valorisation_valide')) if calc else None),
         ('Unit\u00e9s', (not R.get('unites_suspectes')) if calc else None),
         ('Plancher \u221240 %', (R['cap_cours'] >= CAP_MIN) if (calc and num(R.get('cap_cours'))) else None),
         ('Prix', (R.get('porte_prix') == 'ouverte') if calc else None)]
    R['portes'] = P
    return P


def portes_txt(R):
    return ' \u00b7 '.join('%s %s' % (n, '\u2705' if e else '\u26aa' if e is None else '\u274c') for n, e in R.get('portes') or [])


# ------------------------------------------------------------------ verdict final (V22.5.1)
EXCLUSIONS = ('REJET', 'HORS S\u00c9LECTION', 'HORS P\u00c9RIM\u00c8TRE')


def verdict_final(D, R):
    """Toutes les portes en echec sont relevees ; la plus prioritaire (ordre du \u00a712) gouverne,
    les autres restent affichees comme causes secondaires. Un echec de prix ne masque jamais une exclusion,
    et un controle d'achat ne requalifie jamais un dossier deja exclu."""
    meta = D.get('meta') or {}
    prop = G(D, 'verdict.achat') or ''
    ach = str(prop).upper()
    veut = ('ACHAT' in ach or 'RENFORCEMENT' in ach) and 'BLOQU' not in ach
    sur_prix = 'PRIX' in ach or 'WATCHLIST PROCHE' in ach or 'WATCHLIST LOIN' in ach
    exclu = any(k in ach for k in EXCLUSIONS)
    fiab = (meta.get('fiabilite') or 'B').upper()[:1]
    E = []
    if (D.get('qualite') or {}).get('blocage'):
        E.append((1, 'REJET \u2014 STRUCTURE', 'blocage structurel d\u00e9clar\u00e9'))
    if fiab == 'D' and not exclu:
        E.append((2, '\u00c0 DOCUMENTER \u2014 ACHAT BLOQU\u00c9', 'fiabilit\u00e9 D'))
    if not R.get('calc') and veut:
        E.append((2, '\u00c0 DOCUMENTER \u2014 ACHAT BLOQU\u00c9', 'valorisation non ex\u00e9cut\u00e9e (sc\u00e9narios ou cours incomplets)'))
    if R.get('calc'):
        if not R.get('valorisation_valide') and (veut or sur_prix):
            E.append((2, '\u00c0 DOCUMENTER \u2014 ACHAT BLOQU\u00c9', 'ancrage terminal non valid\u00e9'))
        if veut and not R['q']['porte']:
            E.append((4, 'HORS S\u00c9LECTION', 'porte qualit\u00e9 non franchie'))
        if veut and num(R.get('tx_brut')) and R['tx_brut'] > TX_MAX + 1e-9:
            E.append((4, 'HORS S\u00c9LECTION', 'risque au-del\u00e0 de 21 %'))
        if veut and R.get('porte_prix') != 'ouverte':
            cc_, pf_ = R.get('cap_cours'), R.get('PA_fond')
            mot = 'cours au-dessus du prix d\'achat'
            if num(cc_) and cc_ < CAP_MIN:
                mot = ('r\u00e8gle des \u221240 %% : capital pr\u00e9serv\u00e9 %s/100 au cours, prix plancher %s%s'
                       % (fr(cc_, 0), fprix(R.get('P60')),
                          '' if (not num(pf_) or vv(meta.get('cours')) <= pf_ + 1e-9) else ' (et cours au-dessus du prix au taux exig\u00e9)'))
            E.append((6, 'WATCHLIST %s \u2014 PRIX' % ('PROCHE' if R.get('porte_prix') == 'PROCHE' else 'LOIN'), mot))
        if veut and R.get('unites_suspectes'):
            E.append((2, '\u00c0 DOCUMENTER \u2014 ACHAT BLOQU\u00c9', 'incoh\u00e9rence d\u2019unit\u00e9s probable (' + R['unites_suspectes'] + ')'))
        gcas = R.get('guidance_cas')
        if veut and gcas == 'IMPACT NON BORNABLE':
            E.append((2, '\u00c0 DOCUMENTER \u2014 ACHAT BLOQU\u00c9', 'guidance abaiss\u00e9e, impact non bornable'))
        if veut and gcas == 'VETO ACTIF':
            E.append((5, 'WATCHLIST \u2014 GUIDANCE', 'veto de guidance actif'))
        if veut and num(R.get('gc')) and R['gc'] < 5 - 1e-9:
            E.append((7, 'WATCHLIST \u2014 CONFIRMATION', 'croissance centrale par action %s %%/an < 5 %%' % fr(R['gc'], 1)))
        if veut and not R.get('preuves_ok'):
            E.append((7, 'WATCHLIST \u2014 CONFIRMATION', R.get('preuves_motif') or 'confirmations insuffisantes'))
        if veut and num(R.get('part_mult')) and R['part_mult'] > 50:
            E.append((7, 'WATCHLIST \u2014 CONFIRMATION', 'part du multiple >50 %'))
        if ('RENFORCEMENT' in ach and R.get('porte_prix') == 'ouverte' and num(R.get('PR'))
                and vv(meta.get('cours')) > R['PR'] + 1e-9):
            E.append((8, 'ACHAT COMPL\u00c9MENTAIRE POSSIBLE',
                      'cours entre le prix de renforcement (%s) et le prix d\'achat' % fprix(R['PR'])))
    E.sort(key=lambda e: e[0])
    vf = E[0][1] if E else (prop or 'n.d.')
    motifs = [E[0][2]] if E else []
    R['verdict_final'] = vf
    R['verdict_motifs'] = motifs
    R['verdict_secondaires'] = [e[2] for e in E[1:]]
    R['verdict_modifie'] = bool(E) and str(vf).upper() != ach
    if R['verdict_modifie']:
        warn('Verdict %s remplac\u00e9 par %s : %s%s.' % (prop or 'absent', vf, motifs[0],
             (' (aussi : %s)' % ' ; '.join(R['verdict_secondaires'])) if R['verdict_secondaires'] else ''))
    chk('Verdict final contr\u00f4l\u00e9 par le moteur', 'valid\u00e9',
        'inchang\u00e9' if not R['verdict_modifie'] else 'corrig\u00e9 \u2014 %s' % ' ; '.join(motifs + R['verdict_secondaires']))
    return vf


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


def publication_resultats_html(D):
    """Une saisie pour la synthèse du pilote et le détail sourcé de l'épisode 6."""
    pub = G(D, 'resultats.publication')
    if not isinstance(pub, dict) or not pub:
        return '', ''
    date = _date(pub.get('date'))
    date_eval = _date(G(D, 'meta.date_eval'))
    periode, source = pub.get('periode'), pub.get('source')
    if not (date and all(isinstance(s, str) and s.strip() for s in (periode, source))):
        return '', '<p class="sub">Publication à compléter · date, période et source officielle requises.</p>'
    if date_eval and date > date_eval:
        return '', '<p class="sub">Publication postérieure à la date du dossier · écartée de la synthèse.</p>'

    def lignes(cle, limite):
        brut = pub.get(cle)
        return (row for row in brut[:limite] if isinstance(row, list)) if isinstance(brut, list) else ()

    def chiffre(x):
        if not num(x):
            return 'n.d.'
        return fr(x, 4 if 0 < abs(x) < 0.1 else 2).rstrip('0').rstrip(',')

    def ecart(publie, base, unite):
        if not num(base):
            return 'n.d.'
        if unite == '%':
            return fr(publie - base, 1, True) + ' pt'
        if base <= 0:
            return fr(publie - base, 2, True) + ' ' + unite
        return fr((publie / base - 1) * 100, 1, True) + ' %'

    points, rows = [], []
    for row in lignes('chiffres', 3):
        if len(row) < 4:
            continue
        nom, unite, avant, publie, attendu, src, date_attendue = (row + [None] * 7)[:7]
        if not (isinstance(nom, str) and nom.strip() and isinstance(unite, str) and unite.strip() and num(publie)):
            continue
        date_cons = _date(date_attendue)
        if not (num(attendu) and isinstance(src, str) and src.strip() and date_cons and date_cons < date):
            attendu = None
        var_an, surprise = ecart(publie, avant, unite), ecart(publie, attendu, unite)
        points.append('<li><b>%s</b> · %s %s publié · %s · %s</li>' % (
            esc(nom), chiffre(publie), esc(unite),
            esc('%s sur un an' % var_an) if num(avant) else 'période comparable n.d.',
            esc('%s attendu (%s)' % (chiffre(attendu), surprise)) if num(attendu) else 'consensus antérieur n.d.'))
        preuve = '%s · %s' % (src, date_cons.strftime('%d/%m/%Y')) if num(attendu) else 'n.d.'
        rows.append('<tr>' + ''.join('<td>%s</td>' % esc(x) for x in (
            '%s (%s)' % (nom, unite), chiffre(avant), chiffre(attendu), chiffre(publie), var_an, surprise, preuve)) + '</tr>')

    guidance = pub.get('guidance')
    direction = ''
    if isinstance(guidance, list) and guidance:
        etat, horizon, ancien, nouveau = (guidance + [''] * 4)[:4]
        if etat in ('RELEVÉE', 'ABAISSÉE', 'MAINTENUE', 'INITIÉE', 'RETIRÉE', 'NON CHIFFRÉE', 'SANS GUIDANCE', 'N.D.'):
            chemin = ' → '.join(x for x in (ancien, nouveau) if isinstance(x, str) and x.strip())
            direction = '<p><b>Guidance</b> · %s</p>' % esc(' · '.join(
                x for x in (etat, horizon, chemin) if isinstance(x, str) and x.strip()))

    annonces = []
    for row in lignes('annonces', 2):
        if row and isinstance(row[0], str) and row[0].strip():
            annonces.append('<li>%s</li>' % esc(' · '.join(x for x in row[:4] if isinstance(x, str) and x.strip())))
    suites = '<p><b>Ce qui change pour la suite</b></p><ul>%s</ul>' % ''.join(annonces) if annonces else ''
    these = pub.get('these')
    impact = ''
    niveaux = {'RENFORCÉE': 5, 'INCHANGÉE': 'gris', 'FRAGILISÉE': 2}
    if isinstance(these, list) and len(these) == 2 and all(isinstance(s, str) for s in these) and these[0] in niveaux:
        impact = '<p><b>Lecture de la thèse</b> · %s%s</p>' % (
            bdg(these[0], niveaux[these[0]]), ' · ' + esc(these[1]) if these[1].strip() else '')

    if not (points or direction or suites or impact):
        return '', ''
    titre = '<p class="sub">%s · publié le %s</p>' % (esc(periode), date.strftime('%d/%m/%Y'))
    synthese = ('<div class="c"><h3>Que disent les derniers résultats ?</h3>%s%s%s%s%s'
                '<p class="sub"><a href="#publication-resultats">Chiffres et sources · épisode 6</a></p></div>') % (
        titre, '<ul>%s</ul>' % ''.join(points) if points else '', direction, suites, impact)
    table = ('<div class="scroll"><table><tr><th>Indicateur</th><th>Comparable</th><th>Attendu</th>'
             '<th>Publié</th><th>Écart annuel</th><th>Surprise</th><th>Consensus antérieur</th></tr>%s'
             '</table></div>') % ''.join(rows) if rows else ''
    detail = '<div id="publication-resultats">%s%s<p class="sub">Source officielle · %s</p></div>' % (titre, table, esc(source))
    return synthese, detail


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
.b.wrap{white-space:normal;text-align:left;max-width:100%}
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
.roic-box{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;background-color:var(--bg);
background-image:linear-gradient(rgba(57,214,224,.04) 1px,transparent 1px),linear-gradient(90deg,rgba(57,214,224,.04) 1px,transparent 1px);background-size:44px 44px}
.roic-scale{position:relative;display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:3px;margin:30px 0 12px}
.roic-scale span{text-align:center;color:var(--txt2);border-top:5px solid var(--bord);font-size:clamp(9px,2.2vw,13px);padding-top:6px}
.roic-scale .actif{border-color:var(--cy);color:var(--cy)}
.roic-scale b{position:absolute;top:-24px;transform:translateX(-50%);color:var(--cy);line-height:1;font-size:19px}
.roic-badges{display:flex;flex-wrap:wrap;gap:7px;margin:14px 0}
.snow-box{font-family:system-ui,-apple-system,"Segoe UI",sans-serif;background:linear-gradient(135deg,#101f26,#0b1319 65%);padding:30px}
.snow-head{display:flex;align-items:center;justify-content:space-between;gap:18px;flex-wrap:wrap}
.snow-eyebrow{font-size:11px;font-weight:650;letter-spacing:.12em;color:var(--txt2);margin-bottom:7px}
.snow-box h3{font-size:29px;margin:0;color:var(--txt);letter-spacing:-.025em}
.snow-intro{font-size:17px;color:var(--txt2);margin:18px 0 25px;max-width:85ch}
.snow-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:14px;margin-bottom:25px}
.snow-card{padding:22px;border:1px solid #304650;border-radius:13px;background:#101d24;min-width:0}
.snow-question{font-weight:650;font-size:16px;line-height:1.4;margin-bottom:18px}
.snow-number{font-size:35px;font-weight:650;letter-spacing:-.035em;color:var(--txt);line-height:1.15;font-variant-numeric:tabular-nums}
.snow-caption{font-size:12px;color:var(--txt2);margin-top:6px;margin-bottom:16px}
.snow-status{margin:12px 0}.snow-box .b{font-family:inherit;line-height:1.35;font-size:13px;padding:6px 11px}
.snow-card p,.snow-row p{font-size:14px;color:var(--txt2);line-height:1.55;margin:10px 0 0}
.snow-row{display:grid;grid-template-columns:minmax(170px,27%) 1fr;gap:20px;padding:19px 0;border-top:1px solid #2b3d42;font-size:15px}
.snow-row strong{max-width:25ch}.snow-box details{margin-top:0;padding:15px 0;border-top:1px solid #2b3d42}
.snow-box summary{color:var(--txt);font-family:inherit;font-size:14px;font-weight:550}
.snow-box details p{font-size:15px;margin-top:12px}.snow-proof{margin-top:18px;font-size:14px}.snow-proof p{margin:5px 0 0;color:var(--txt2)}
.snow-missing{margin-top:20px;font-size:14px}.snow-missing ul{margin-top:10px;padding-left:18px;list-style:disc}.snow-missing li{padding:0;margin:6px 0;font-size:14px}.snow-missing li::before{content:none}
.snow-box .capital-box{margin-top:20px;background:transparent;border-color:var(--bord)}
.snow-footnote{font-size:12px;color:var(--txt2);margin:12px 0 0;max-width:95ch}
@media(max-width:820px){.snow-grid{grid-template-columns:1fr}.snow-row{grid-template-columns:1fr;gap:9px}.snow-box{padding:22px}.snow-box h3{font-size:25px}.snow-card{padding:20px}}
@media print{.snow-box,.snow-card{background:white;color:black}.snow-number,.snow-box h3,.snow-question,.snow-box summary{color:black}}
.ep{margin:70px 0 20px;padding-top:24px;border-top:1px solid var(--cy2)}
.ep-n{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:13px;letter-spacing:.16em;color:var(--cy)}
.ep h2{font-family:"Iowan Old Style","Charter",Georgia,serif;font-size:31px;line-height:1.2;color:var(--txt);margin:8px 0 10px;letter-spacing:-.01em}
.ep-c{color:var(--txt2);font-size:18px;max-width:80ch;margin:0}
.enclair{border-left:3px solid var(--cy);border-radius:0 12px 12px 0;background:rgba(57,214,224,.07);padding:16px 20px;margin:0 0 22px;font-size:19px;line-height:1.6}
details.coul{margin-top:40px;border:1px dashed var(--bord);border-radius:12px;padding:14px 18px}
details.coul>summary{color:var(--cy);font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:14px}
@media(max-width:480px){.ep h2{font-size:25px}}
.gen{display:grid;grid-template-columns:1fr auto 1fr auto 1fr auto 1fr;gap:10px;align-items:stretch;margin-top:18px}
.gen-e{border:1px solid var(--bord);border-radius:14px;padding:16px 18px;background:var(--carte)}
.gen-v{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:30px;font-weight:700;margin:6px 0 10px}
.gen-f{align-self:center;color:var(--cy);font-size:24px}
.feux{display:flex;align-items:center;gap:14px;margin:14px 0;padding:12px 18px;border:1px solid var(--bord);border-radius:12px;font-size:18px}
.feu{display:inline-block;width:14px;height:14px;border-radius:50%;margin-right:6px}
@media(max-width:900px){.gen{grid-template-columns:1fr}.gen-f{transform:rotate(90deg);justify-self:center}}
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
        ('Combien rapporte la machine ?', 'Dernier %s : %s %% · médiane : %s %% · coût du capital : %s %%' % (esc(rb.get('metrique', 'ROIC')), fr(rb['last']), fr(rb['med']), fr(rb['wacc']))),
        ('Est-elle durable ?', 'Mesurée : ' + qual_badge(rb.get('tend') or 'INCONNUE') + (' pente %s pts/an' % fr(rb.get('pente'), 1, True) if num(rb.get('pente')) else '') + ' · déclarée : ' + qual_badge(rent.get('tendance')) + qual_texte(rent.get('tendance_preuve'))),
        ('Les nouveaux euros travaillent-ils aussi bien ?', qual_badge(rent.get('nouveaux_investissements')) + qual_texte(rent.get('rendement_incremental'))),
        ('Peut-elle grossir ?', qual_texte(rent.get('reinvestissement'))),
        ('Le chiffre est-il trompeur ?', qual_texte(rent.get('vigilance_comptable'))),
    ]
    a = '<section class="c capital-box"><h3>La machine à créer du profit</h3><p class="sub">Chaque euro supplémentaire investi crée-t-il suffisamment de profit après impôt, et combien peut-on encore investir ainsi ?</p><table>'
    a += ''.join('<tr><th>%s</th><td>%s</td></tr>' % (esc(k), v) for k, v in rows)
    a += '</table><p class="sub">Source : ' + qual_texte(rent.get('source')) + '</p><p class="sub">ROIC après impôt ; AT ROCE comparable seulement à définition cohérente. Rentabilité économique ≠ rendement boursier.</p></section>'
    # V23.1 : encadre Marge brute retire du dossier (demande de Nico, 30/10/2026) ; le champ reste lu si present, sans affichage.
    return a



def _meur(x):
    if not num(x):
        return 'n.d.'
    return ('%s M€' % fr(x / 1e6, 1)) if abs(x) >= 1e6 else ('%s k€' % fr(x / 1e3, 0))


def inities_html(D, R):
    """V22.9 : rectangle dedie aux inities (flux de marche, argent propre)."""
    I = R.get('init') or {}
    lab = I.get('lab') or 'NON VÉRIFIÉ'
    lvl = I.get('lvl', 'gris')
    bord = {6: 'var(--l5)', 5: 'var(--l5)', 4: 'var(--l4)', 3: 'var(--l3)', 2: 'var(--l2)', 1: 'var(--l1)'}.get(lvl, 'var(--gris)')
    cours = vv((D.get('meta') or {}).get('cours'))
    o = ['<div class="c" style="border:2px solid %s"><h3>\U0001f454 Initiés — ce que les dirigeants font de leur propre argent</h3>' % bord]
    o.append('<div>%s</div>' % bdg(lab, lvl, 'gros'))
    if lab == 'NON VÉRIFIÉ':
        o.append('<p class="sub">Transactions des dirigeants non vérifiées dans ce dossier%s. '
                 'Le contrôle est en échec : relancer avec inities.transactions.</p></div>' % (
                     (' (ancien badge : %s)' % esc(I.get('legacy'))) if I.get('legacy') else ''))
        return ''.join(o)
    pxa, pxv = I.get('px_achat'), I.get('px_vente')
    comp = ''
    if num(pxa) and num(cours):
        e = 100 * (cours / pxa - 1)
        comp = 'cours %s %s %% vs leur prix moyen' % (fprix(cours), fr(e, 0, True))
    o.append('<div class="grid g4" style="margin-top:16px">')
    o.append(carte('Achats de marché · 12 mois', _meur(I.get('a12')), 5 if I.get('a12') else 'gris',
                   '%s %% de la capitalisation · %s acheteur(s)' % (fr(I.get('pct_a'), 2), I.get('nb_ach', 0))))
    o.append(carte('Ventes de marché · 12 mois', _meur(I.get('v12')), 2 if I.get('v12') else 'gris',
                   '%s %% de la capitalisation · %s vendeur(s)' % (fr(I.get('pct_v'), 2), I.get('nb_vend', 0))))
    o.append(carte('Prix moyen payé par les initiés', fprix(pxa) if num(pxa) else 'n.d.', 5 if num(pxa) else 'gris', comp or '—'))
    o.append(carte('Dernier achat', esc(I.get('dernier_achat') or 'aucun'), 5 if I.get('dernier_achat') else 'gris',
                   ('il y a %s mois' % fr(I.get('mois_dernier_achat'), 0)) if num(I.get('mois_dernier_achat')) else '—'))
    o.append('</div>')
    o.append('<p style="margin-top:6px"><b>Effet dans le moteur :</b> %s.</p>' % esc(I.get('effet')))
    if num(pxv):
        o.append('<p class="sub">Prix moyen des ventes : %s%s.</p>' % (fprix(pxv), (
            ' — %s %% du range 52 semaines' % fr(100 * I['pos_vente'], 0)) if num(I.get('pos_vente')) else ''))
    if I.get('lignes'):
        rows = ''.join('<tr><td>%s</td><td>%s<div class="sub" style="margin:0">%s</div></td><td class="t%s">%s</td><td>%s</td>'
                       '<td class="n">%s</td><td class="n">%s</td></tr>' % (
            esc(l['date']), esc(l['nom']), esc(l['fonction'] or ''), 5 if l['sens'] == 'ACHAT' else 2, l['sens'],
            esc(l['nature']) + ('' if l['compte'] else ' · non comptée'), _meur(l['montant']), fprix(l['prix']) if num(l['prix']) else 'n.d.')
            for l in sorted(I['lignes'], key=lambda l: l['age'] if l['age'] is not None else 9e9))
        o.append('<details open><summary>Transactions retenues</summary><div class="scroll"><table>'
                 '<tr><th>Date</th><th>Qui</th><th>Sens</th><th>Nature</th><th class="n">Montant</th><th class="n">Prix</th></tr>%s</table></div></details>' % rows)
    o.append('<div class="sub">Seuil d’un flux fort : %s nets sur 12 mois (0,10 %% de la capitalisation, 250 k€ au moins), '
             'ou au moins 3 dirigeants dans le même sens en 90 jours. Seuls les achats et ventes de marché comptent : '
             'options, plans, attributions et ventes fiscales sont affichés sans être comptés. Source : %s.</div></div>' % (
                 _meur(I.get('seuil')), esc(I.get('source') or 'non nommée')))
    return ''.join(o)


def plancher_html(R):
    """V22.7 : bloc « Ce qu'il te reste si tu t'es trompé »."""
    if not R.get('calc'):
        return ''
    cc, cpa = R.get('cap_cours'), R.get('cap_PA')
    b = R.get('baissier') or {}
    pos = lambda x: max(0.0, min(100.0, x)) if num(x) else None
    zones = [(0, 60, '#f0605f', 'perte > 40 %'), (60, 70, '#f3a33b', 'fragile'),
             (70, 85, '#9edb6b', 'solide'), (85, 100, '#2dc7c9', 'forteresse')]
    seg = ''.join('<div class="seg" style="left:%s%%;width:%s%%;background:%s"></div>' % (a, b_ - a, c) for a, b_, c, _ in zones)
    lab = ''.join('<div class="tick" style="left:%s%%;top:70px">%s</div>' % ((a + b_) / 2, l) for a, b_, _, l in zones)
    cur = ''
    if num(cc):
        cur += '<div class="cur" style="left:clamp(60px,%s%%,calc(100%% - 60px))">\u25b2 au cours %s</div>' % (pos(cc), fr(cc, 0))
    if num(cpa):
        cur += ('<div class="tick" style="left:%s%%;top:96px;color:var(--cy)">\u25b3 au prix max. d\u2019achat %s</div>' % (pos(cpa), fr(cpa, 0)))
    tests = ''.join('<tr><td>%s</td><td>%s</td><td class="b">%s</td></tr>' % (
        esc(t[0]), '\u2705' if t[1] else '\u26aa' if t[1] is None else '\u274c', esc(t[2])) for t in b.get('tests') or [])
    conds = ''.join('<tr><td>%s</td><td>%s</td><td class="b">%s</td></tr>' % (
        esc(c[0]), '\u2705' if c[1] else '\u274c', esc(c[2])) for c in R.get('B_cond') or [])
    lim = ''
    if R.get('plancher_limite') and num(R.get('PA')):
        lim = ('<p><b>Le prix maximum d\u2019achat est limité par la règle des \u221240 %%</b> : %s au lieu de %s au seul taux exigé.</p>'
               % (fprix(R['PA']), fprix(R.get('PA_fond'))))
    elif R.get('plancher_limite'):
        lim = '<p><b>Aucun prix ne respecte la règle des \u221240 %</b> dans ce baissier : achat impossible.</p>'
    eff = []
    if R.get('B_actif'):
        eff.append('taux exigé \u22121 pt (plancher prouvé)')
    if R.get('forteresse'):
        eff.append('\U0001f3f0 forteresse : plafond de taille +1 pt')
    if num(cc) and CAP_MIN <= cc < CAP_SOLIDE:
        eff.append('plancher fragile : taille plafonnée à 3 %')
    if b.get('lab') == 'DOUTEUX':
        eff.append('baissier douteux : taille plafonnée à 3 %, aucun bonus')
    return ('<div class="c capital-box"><h3>\U0001f6e1\ufe0f Ce qu\u2019il te reste si tu t\u2019es trompé</h3>'
            '<p class="sub">Capital préservé du scénario baissier à 4 ans, dividendes compris. Sous 60/100, la perte dépasse 40 %% : '
            'c\u2019est la règle « au-delà de \u221240 %%, je me suis trompé ». Le prix maximum sous la règle des \u221240 %% est le cours le plus haut qui garde 60/100 : '
            'il ne contraint que s\u2019il passe sous le prix maximum d\u2019achat.</p>'
            '<div class="rl" style="height:120px;margin-top:40px">%s%s%s</div>'
            '<div class="grid g3">%s%s%s</div>%s'
            '<div style="margin:10px 0">%s %s</div>'
            '<details><summary>Crédibilité du baissier \u2014 les tests</summary><div class="scroll"><table>%s</table></div></details>'
            '<details><summary>Modificateur « plancher prouvé » (\u22121 pt) \u2014 les conditions</summary><div class="scroll"><table>%s</table></div></details>'
            '</div>') % (
        seg, lab, cur,
        carte('Capital préservé au cours', '%s /100' % fr(cc, 0), L_CAP(cc), 'si le baissier arrive'),
        carte('Au prix maximum d\u2019achat', '%s /100' % fr(cpa, 0), L_CAP(cpa), 'si tu achètes au plus haut autorisé (%s)' % fprix(R.get('PA'))),
        carte('Prix max. sous la règle \u221240 %', fprix(R.get('P60')), 5 if not R.get('plancher_limite') else 3,
              'contraignant : il fixe le prix maximum d\u2019achat' if R.get('plancher_limite') else
              'non contraignant : au-dessus du prix maximum d\u2019achat (%s)' % fprix(R.get('PA'))),
        lim, bdg('Baissier ' + b.get('lab', 'n.d.'), b.get('lvl', 'gris')),
        ' '.join(bdg(e, 4) for e in eff) or '<span class="sub">aucun effet sur le taux ni sur la taille</span>',
        tests or '<tr><td>n.d.</td></tr>', conds or '<tr><td>n.d.</td></tr>')


def rendu(D, R):
    meta = D.get('meta') or {}
    valo = D.get('valo') or {}
    cours = vv(meta.get('cours')); dev = meta.get('devise', '')
    resultats_pilote, resultats_detail = _sur(publication_resultats_html, D, defaut=('', ''))
    BK = {}
    _cur = ['tete']

    def A(s_):
        BK.setdefault(_cur[0], []).append(s_)

    def S_(nom):  # V23.7 : chaque bloc va dans un tiroir, assemble ensuite en episodes
        _cur[0] = nom
    A('<!doctype html><html lang="fr"><head><meta charset="utf-8">')
    A('<meta name="viewport" content="width=device-width,initial-scale=1">')
    A('<title>Dossier %s \u2014 %s</title><style>%s%s%s</style></head><body><div class="wrap">' % (
        esc(meta.get('societe')), esc(meta.get('ticker')), CSS, CSS_V24, CSS_V25))

    # -- en-tete
    A('<div class="p0">Dossier NICO %s · évalué le %s · cours du %s · %s · <span title="A faits officiels · B solides · C incertitude bornée · D invérifiable">fiabilité %s</span> · taux exigé %s\u00a0%%/an · %s</div>' % (
        VERSION, esc(meta.get('date_eval')), esc(meta.get('date_cours')), esc(meta.get('bourse')),
        esc(meta.get('fiabilite')), fr(R.get('tx'), 1), ('ligne détenue (PF)' if R.get('detenue') else esc(meta.get('mode', 'nouvelle position')))))

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
        A('<p class="sub">Empreinte des hypothèses : %s. Un autre cours ou un autre taux de change du jour ne modifie pas cette empreinte (la valeur en euros, elle, peut bouger).</p></div>' % esc(R.get('empreinte_hypotheses')))
    al = R.get('alignement')
    S_('coulisses')
    if R.get('calc'):
        A('<div class="sub" style="margin:6px 0 14px">Horizon : %s</div>' % (
            ('exercices projet\u00e9s clos du %s au %s \u00b7 sortie le %s sur le BPA des 12 mois glissants%s \u00b7 dividendes \u00e0 cl\u00f4ture + %s mois'
             % (al['clotures'][1], al['clotures'][4], al['sortie'],
                (' (dont %s mois prolong\u00e9s au rythme prudent)' % fr(al.get('extrapolation_mois'), 0)) if (al.get('extrapolation_mois') or 0) >= 0.5 else '',
                fr(al['delai_mois'], 0))) if al else
            'exercices non dat\u00e9s \u2014 convention par d\u00e9faut (cl\u00f4tures aux anniversaires de l\u2019\u00e9valuation)'))
    S_('pilote')
    if R.get('calc') and not R.get('valorisation_valide'):
        A('<div class="c" style="border-color:var(--l2)">Prix indicatifs uniquement : ancrage terminal à corriger avant toute décision.</div>')
    # -- verdict
    v = D.get('verdict') or {}
    A(_sur(page1_html, D, R))  # V25 : la page 1 qui se lit comme on parle
    A('<div class="tdb-titre">📊 LE TABLEAU DE BORD · LES CHIFFRES DERRIÈRE LA PAGE 1</div>')
    A(_sur(action_html, D, R))  # V24 : que faire (version technique)
    A('<div class="c"><div class="lab" style="margin-bottom:8px">Verdict de la Voie A (garder 3 à 5 ans) · décision de suivi</div><div>%s &nbsp; %s</div><p style="margin-top:10px;font-size:16px">%s</p>'
      '<div class="sub">%s%s</div></div>' % (
          bdg(R.get('verdict_final') or v.get('achat', 'n.d.'), L_LAB('achat', R.get('verdict_final')), 'gros'),
          bdg(v.get('suivi', 'n.d.'), L_LAB('suivi', v.get('suivi')), 'gros'),
          esc(v.get('phrase')), esc(v.get('cause')),
          ' \u00b7 ' + esc(v.get('cause2')) if v.get('cause2') else ''))
    A(flags_html(R))  # V23 : red flags ethique / Etat / forensique, sans blocage
    A(resultats_pilote)
    if not (R.get('recit') or {}).get('chapeau'):
        A(fait_cle_html(R))  # V24 : le fait qui explique le prix (repris par la page 1 sinon)
    A(_sur(pilote_html, D, R))  # V23.7 : les trois reponses + capital preserve + phrase en clair
    A(_sur(pari_html, D, R))  # V24 : asymetrie, esperance, confiance
    _B = R.get('voie_b') or {}
    A('<div class="c"><h3>Les portes de l\u2019achat</h3><div>%s</div><div class="sub">Voie A : il faut tout en vert ; '
      '\u26aa = non \u00e9valu\u00e9.</div><div style="margin-top:14px;line-height:2.4">'
      '<span class="lab" style="margin-right:10px">Les deux voies :</span>%s &nbsp; %s</div></div>' % (' '.join(
          bdg(('\u2705 ' if e else '\u26aa ' if e is None else '\u274c ') + n, 5 if e else 'gris' if e is None else 2)
          for n, e in portes(D, R)),
          bdg('Voie A (3–5 ans) : %s' % (R.get('verdict_final') or 'n.d.'), L_LAB('achat', R.get('verdict_final')), 'wrap'),
          bdg('Voie B (12–18 mois) : %s' % (_B.get('lab') or 'n.d.').replace('VOIE B ', '').replace('VOIE A OUVERTE', 'sans objet'),
              _B.get('lvl', 'gris'), 'wrap') if _B else ''))
    if R.get('verdict_modifie'):
        A('<div class="c" style="border-color:var(--l3)"><b>Verdict corrig\u00e9 par le moteur.</b> '
          'Le dossier proposait \u00ab %s \u00bb ; les contr\u00f4les l\'interdisent : %s.</div>' % (
              esc(v.get('achat')), esc(' ; '.join((R.get('verdict_motifs') or []) + [
              'aussi : ' + x for x in (R.get('verdict_secondaires') or [])]))))

    q = R['q']
    S_('coulisses')

    mr = ''.join('<tr><td>%s</td><td class="n t%s">%s pt</td></tr>' % (
        esc(lab), 5 if d < 0 else 3, fr(d, 1, True)) for lab, d in (R.get('tx_mods') or []))
    if not mr:
        mr = '<tr><td>aucun modificateur retenu</td><td class="n">0 pt</td></tr>'
    A('<div class="c"><h3>Taux exig\u00e9 de la ligne \u2014 %s %%/an</h3>'
      '<div class="sub">Base 15 %%, born\u00e9 12\u201321 %%. Ce taux ne facture que le risque '
      '<b>non mod\u00e9lisable dans les flux</b> (juridiction, liquidit\u00e9, perte irr\u00e9versible) : '
      'ce qui est d\u00e9j\u00e0 chiffr\u00e9 dans le sc\u00e9nario baissier ou dans le multiple terminal n\'y figure pas : un risque ne se paie qu\'une fois.</div>'
      '<div class="scroll"><table>%s<tr><td><b>Taux exig\u00e9 retenu</b></td><td class="n"><b>%s %%</b></td></tr></table></div>%s</div>' % (
          fr(R.get('tx'), 1), mr, fr(R.get('tx'), 1),
          '<div class="sub">Valeur born\u00e9e \u00e0 l\'intervalle 12\u201321 %.</div>' if R.get('tx_borne') else ''))

    S_('plancher')
    A(plancher_html(R))
    S_('coulisses')
    A('<div class="sub" style="margin:6px 0 14px">Tri rapide : %s. Les scores sont des conventions de s\u00e9lection en %%, pas des probabilit\u00e9s.</div>' % esc(meta.get('tri')))

    S_('ep1')
    # -- ACTE 0
    a0 = D.get('acte0') or {}
    th = a0.get('these') or {}
    nbm, nbp = compter_these(th.get('texte'))
    rev = ''.join('<tr><td>%s</td><td class="n">%s</td><td class="n">%s</td><td>%s</td></tr>' % (
        esc(r[0]), esc(r[1]), esc(r[2] if len(r) > 2 else ''), prov(r[3] if len(r) > 3 else '')) for r in (a0.get('revenus') or []))
    A('<div class="grid g2">')
    A('<div class="c"><h3>Ce qu\'elle fait</h3>'
      '<p><b>Activit\u00e9</b> \u2014 %s</p><p><b>Positionnement</b> \u2014 %s</p><p><b>Perspectives</b> \u2014 %s</p>'
      '<div class="scroll"><table>%s</table></div><div class="sub">%s %s</div></div>' % (
          esc(a0.get('activite')), esc(a0.get('positionnement')), esc(a0.get('perspectives')), rev,
          esc(V(a0.get('ratio_echelle'))['v']), prov(V(a0.get('ratio_echelle'))['prov'])))
    A('<div class="c"><h3>La th\u00e8se en 80 mots</h3><p>%s</p>'
      '<div class="sub">%s mots \u00b7 %s phrases%s</div></div>' % (
          esc(th.get('texte')), nbm, nbp,
          '' if (nbm <= 80 and 3 <= nbp <= 4) else ' \u2014 <span class="t3">hors format</span>'))
    A('</div>')

    # -- V22.8 : le probleme existera-t-il encore ?
    avr = R.get('avenir') or {}
    if avr.get('doc'):
        A('<div class="c"><h3>\U0001f52e Le problème existera-t-il encore ?</h3>'
          '<p><b>Problème résolu</b> — %s</p><div class="grid g3">'
          '<div><div class="lab">Le besoin demain</div><div>%s</div><div class="sub">%s</div></div>'
          '<div><div class="lab">La société en gardera-t-elle la valeur ?</div><div>%s</div><div class="sub">%s</div></div>'
          '<div><div class="lab">Lecture</div><div>%s</div><div class="sub">%s</div></div></div>'
          '<div class="sub">Lecture seulement : les faits se notent dans Modèle 2 et Modèle 3, '
          'aucun point ni effet sur le prix. Un besoin croissant ne garantit pas des profits croissants.</div></div>' % (
              esc(avr.get('probleme') or 'n.d.'),
              bdg(avr.get('ex'), avr.get('ex_lvl', 'gris')), esc(avr.get('ex_txt')),
              bdg(avr.get('ca'), avr.get('ca_lvl', 'gris')), esc(avr.get('ca_txt')),
              bdg(avr.get('synth'), avr.get('lvl', 'gris')), esc(avr.get('txt'))))
    else:
        A('<div class="c"><h3>\U0001f52e Le problème existera-t-il encore ?</h3><div>%s</div>'
          '<div class="sub">Rubrique non renseignée dans ce dossier.</div></div>' % bdg('NON DOCUMENTÉ', 'gris'))
    A(profil_html(D, R))  # V23 : fiche de tri

    # -- bande compacte
    sec = D.get('secteur') or {}
    rb = R['rentab']
    st = G(D, 'risques.stress') or {}
    d_pire = min([x for x in (st.get('d_bas'), st.get('d_haut')) if num(x)] or [None]) if any(num(st.get(k)) for k in ('d_bas', 'd_haut')) else None
    S_('vent' if (num(sec.get('s_bas')) or num(sec.get('s_haut'))) else 'masque')  # V24 : bloc vide -> angles morts
    A('<div class="c"><div class="lab">Vent sectoriel</div><div>%s</div><div class="sub">%s \u00b7 %s %s</div></div>' % (
        bdg('%s \u00e0 %s %%/an' % (fr(sec.get('s_bas'), 1), fr(sec.get('s_haut'), 1)), L_SECT(sec.get('s_bas'))),
        esc(sec.get('perimetre')), esc(sec.get('periode')), prov(sec.get('prov'))))
    S_('risq_cartes')
    A('<div class="c"><div class="lab">Stress pouvoir d\'achat \u221220 %%</div><div>%s</div><div class="sub">%s</div></div>' % (
        bdg('%s \u00e0 %s %% de r\u00e9sultat op. an 4' % (fr(st.get('d_bas'), 0), fr(st.get('d_haut'), 0)), L_D(d_pire)),
        esc(st.get('mecanisme'))))

    # ---------------- bloc 1
    S_('resultats')
    ial = V(G(D, 'risques.ia'))['v']
    pp = V(G(D, 'qualite.pouvoir_prix'))
    res = D.get('resultats') or {}
    rp = res.get('reperes') or {}
    cells = ''.join('<td class="n">%s %%</td>' % fr(rp.get(k), 1, True) for k in ('ca_n1', 'ca_attentes', 'bpa_n1', 'bpa_attentes'))
    A('<div class="c"><h3>Derniers r\u00e9sultats et guidance</h3><div>%s</div>'
      '<div class="scroll"><table><tr><th class="n">CA vs N\u22121</th><th class="n">CA vs attentes</th>'
      '<th class="n">BPA vs N\u22121</th><th class="n">BPA vs attentes</th></tr><tr>%s</tr></table></div>'
      '%s<p>%s</p><div class="sub">Confirmations : %s</div></div>' % (
          bdg(res.get('verdict', 'IND\u00c9TERMIN\u00c9'), L_LAB('resultats', res.get('verdict'))), cells,
          resultats_detail, esc(res.get('guidance') or res.get('commentaire')), esc(' \u00b7 '.join((' \u2014 '.join(str(y) for y in c if y) if isinstance(c, list) else str(c))
                                for c in (res.get('confirmations') or []) if c))))
    rows = ''.join('<tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>' % (
        esc(r.get('fait')), esc(r.get('mecanisme')), esc(r.get('gravite')), esc(r.get('indicateur')), esc(r.get('hypothese')))
        for r in (G(D, 'risques.registre') or []))
    S_('registre')
    A('<div class="c"><h3>Registre des risques</h3><div class="scroll"><table>'
      '<tr><th>Fait</th><th>M\u00e9canisme</th><th>Gravit\u00e9</th><th>Indicateur avanc\u00e9</th><th>Hypoth\u00e8se</th></tr>%s</table></div>'
      '<div style="margin-top:10px">%s %s</div><div class="sub">%s</div></div>' % (
          rows, bdg('IA : %s' % (ial or 'IND\u00c9TERMIN\u00c9'), L_LAB('ia', ial)),
          bdg('Cycle capex IA : %s' % (V(G(D, 'risques.capex_ia'))['v'] or 'IND\u00c9TERMIN\u00c9'),
              L_LAB('capex', V(G(D, 'risques.capex_ia'))['v'])),
          esc(V(G(D, 'risques.ia'))['prov'])))

    # ---------------- bloc 2
    S_('piliers')
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
    A('<div class="c"><h3>Six piliers</h3>%s<div class="sub">Q = %s %% \u00b7 couverture %s %%%s</div></div>' % (
        ''.join(barres), fr(q['Q'], 0), fr(q['cov'], 0),
        ' \u00b7 contr\u00f4les inconnus : ' + esc(', '.join(inconnus)) if inconnus else ''))
    S_('boule')
    A(capital_html(D, R))
    S_('valeur' if (R.get('valeur') or {}).get('doc') else 'masque')  # V24 : bloc vide -> angles morts
    A(valeur_html(R))  # V23 : creation de valeur

    S_('moatdir')
    A('<div class="grid g2"><div class="c"><h3>Moat et pouvoir de prix</h3><p>%s</p><div>%s</div><div class="sub">%s</div></div>'
      '<div class="c"><h3>Direction, initi\u00e9s et alignement</h3><p>%s</p><div>%s %s %s</div><div class="sub">%s</div></div></div>' % (
          esc(G(D, 'qualite.moat')), bdg('Pouvoir de prix : %s' % (pp['v'] or 'IND\u00c9TERMIN\u00c9'), L_LAB('prix', pp['v'])),
          esc(pp['prov'] or pp['src'] or G(D, 'qualite.pouvoir_prix_preuve') or ''),
          esc(G(D, 'qualite.direction_txt')),
          bdg('Initi\u00e9s : %s' % ((R.get('init') or {}).get('lab') or 'NON V\u00c9RIFI\u00c9'),
              (R.get('init') or {}).get('lvl', 'gris')),
          bdg(V(G(D, 'gouvernance.actionnariat'))['v'] or 'NON DOCUMENT\u00c9',
              L_LAB('actionnariat', V(G(D, 'gouvernance.actionnariat'))['v'])),
          bdg('KPI : %s' % (V(G(D, 'gouvernance.kpi'))['v'] or 'NON PUBLI\u00c9'),
              L_LAB('kpi', V(G(D, 'gouvernance.kpi'))['v'])),
          esc(G(D, 'gouvernance.synthese'))))
    A(inities_html(D, R))  # V23.1 : rectangle des initiés juste sous « Direction, initiés et alignement »

    S_('traj')
    tb = R.get('tableau_aff') or {}
    if tb.get('annees'):
        ne = tb.get('n_estime', 0)
        thh = ''.join('<th class="n">%s</th>' % esc(a) for a in tb['annees'])
        trs = ''
        for nom, serie in (tb.get('lignes') or []):
            _cn = COUL_BPA if nom.upper().startswith('BPA') else COUL_FCF if nom.upper().startswith('FCF') else None
            trs += '<tr><td%s>%s</td>%s</tr>' % ((' style="color:%s;font-weight:600"' % _cn) if _cn else '', esc(nom), ''.join(
                '<td class="n%s">%s</td>' % (' tgris' if (ne and i >= len(tb['annees']) - ne) else '', fr(x, 2 if abs(x) < 10 else 1) if num(x) else 'n.d.')
                for i, x in enumerate(serie)))
        A('<div class="c"><div class="scroll"><table><tr><th></th>%s</tr>%s</table></div>'
          '<p>%s</p><p class="sub">%s</p><div>%s</div></div>' % (
              thh, trs, esc(G(D, 'croissance.moteurs')), esc(G(D, 'croissance.convergence')),
              bdg('Protection : %s' % (V(G(D, 'croissance.protection'))['v'] or 'non document\u00e9e'),
                  L_LAB('protection', V(G(D, 'croissance.protection'))['v']), 'wrap')))

    # ---------------- bloc 3
    S_('prix_tri')
    tol = R.get('tolerance')
    A('<div class="grid g3">%s%s%s</div>' % (
        carte('Multiple de sortie exig\u00e9 par le cours', ('%s\u00d7' % fr(R.get('mult_exige'), 1)) if num(R.get('mult_exige')) else 'n.d.',
              L_LAB('mult_exige', R.get('mult_exige_lab')),
              'pour %s %%/an nets \u00b7 central %s\u00d7 \u00b7 %s' % (fr(R.get('tx'), 1), fr(G(D, 'valo.scenarios.central.multiple'), 1),
                                                   esc(R.get('mult_exige_lab', 'n.d.')).lower())),
        (carte('Central contre rythme historique',
              ('%s pts' % fr(R.get('ecart_hist'), 1, True)) if num(R.get('ecart_hist')) else 'n.d.',
              L_ECART(R.get('ecart_hist')),
              'croissance centrale par action moins croissance organique pass\u00e9e') if (num(R.get('ecart_hist')) or not num((R.get('sources_g') or {}).get('passe'))
                                                                                    or not num(R.get('gc'))) else
         carte('Central contre BPA pass\u00e9', '%s pts' % fr(R['gc'] - R['sources_g']['passe'], 1, True), L_ECART(R['gc'] - R['sources_g']['passe']),
               'central %s %%/an contre %s %%/an publi\u00e9s : %s' % (fr(R['gc'], 1), fr(R['sources_g']['passe'], 1),
               'le central promet un retournement, il doit \u00eatre prouv\u00e9' if R['gc'] - R['sources_g']['passe'] > 3 else 'pas d\u2019acc\u00e9l\u00e9ration promise'))),
        carte('Si le mauvais sc\u00e9nario arrive t\u00f4t', '%s %%/an' % fr(R.get('tri_bear_25'), 1),
              L_RDT(R.get('tri_bear_25')), 'revente forc\u00e9e au bout de 2 ans et demi')))

    S_('prix')
    # barrette decisionnelle : seulement les niveaux actionnables au-dessus de l'objectif
    PA, PR, PS = R.get('PA'), R.get('PR'), R.get('PS')
    ta = R.get('tx_action') or (15.0, 18.0, 21.0)
    if all(num(x) for x in (PA, PR, PS)):
        hi = max(PA * 1.15, cours * 1.15)
        pc = lambda p: max(0.0, min(100.0, 100 * p / hi))
        segs = [(0, pc(PS), '#2dc7c9'), (pc(PS), pc(PR), '#4ede9a'),
                (pc(PR), pc(PA), '#9edb6b'), (pc(PA), 100, '#f0605f')]
        sg = ''.join('<div class="seg" style="left:%s%%;width:%s%%;background:%s"></div>' % (a, max(0.4, b - a), c) for a, b, c in segs)
        tk = ''.join('<div class="tick" style="left:clamp(84px,%s%%,calc(100%% - 84px));top:%spx">%s \u00b7 %s %% \u00b7 %s</div>' %
                     (pc(p), top, lib, fr(t, 0), fprix(p)) for p, t, lib, top in
                     ((PS, ta[2], 'Forte marge', 70), (PR, ta[1], 'Renfort', 92),
                      (PA, ta[0], 'Prix max.' + (' (r\u00e8gle \u221240 %)' if R.get('plancher_limite') else ''), 114)))
        A('<div class="c"><h3>Barrette de prix (%s)</h3><div class="rl">%s%s'
          '<div class="cur" style="left:clamp(96px,%s%%,calc(100%% - 96px))">\u25b2 cours %s \u2192 %s %%/an</div></div>'
          '<div class="sub">Prix maximum d\u2019achat (%s %%/an) : %s \u00b7 renfort %s %% : %s \u00b7 forte marge %s %% : %s. '
          'Cours du jour : %s \u2192 %s %%/an. Aucun palier sous le prix maximum d\u2019achat n\'est affich\u00e9.</div></div>' % (
              esc(dev), sg, tk, pc(cours), fprix(cours), fr(R.get('retenu'), 1),
              fr(ta[0], 0), fprix(PA), fr(ta[1], 0), fprix(PR), fr(ta[2], 0), fprix(PS),
              fprix(cours), fr(R.get('retenu'), 1)))

    srows = ''
    for nom in ('baissier', 'central', 'haussier'):
        sc = (valo.get('scenarios') or {}).get(nom)
        if not sc or 'ctx' not in R:  # arret precoce : pas de scenarios chiffres
            continue
        t_ = tri(flux(cours, sc, R['ctx'])[0])
        pt = val_term(sc, R['ctx'])
        tns, pfs = tn_sc(sc, R['ctx'])
        if tns or pfs:
            sc = dict(sc); sc['txt'] = ('Valeur \u00e0 4 ans = exploitation %s \u00d7 %s + tr\u00e9sorerie nette %s. ' % (
                fr(bpa_at(sc, R['ctx']['base'], 4.0, R['ctx']['gt'], R['ctx'].get('tk')) - pfs, 2), fr(sc['multiple'], 1),
                fprix(tns))) + (sc.get('txt') or '')
        srows += ('<tr><td><b>%s</b></td><td class="n">%s %%</td><td class="n">%s</td><td class="n">%s\u00d7</td><td class="n">%s</td>'
                  '<td class="n t%s">%s %%/an</td></tr><tr class="scn"><td colspan="6">%s</td></tr>') % (
                     nom.capitalize(), fr(100 * sc.get('poids', POIDS_DEF[nom]), 0), fr(sc['bpa'][3], 2),
                     fr(sc['multiple'], 1), fprix(pt), L_RDT(t_) if L_RDT(t_) != 'gris' else 'gris', fr(t_, 1), esc(sc.get('txt', '')))
    A('<div class="c"><h3>Trois sc\u00e9narios \u00e0 quatre ans</h3><div class="scroll"><table class="sc">'
      '<tr><th>Sc\u00e9nario</th><th class="n">Poids</th><th class="n">BPA an 4</th><th class="n">Multiple</th>'
      '<th class="n">Valeur \u00e0 4 ans</th><th class="n">TRI</th></tr>%s</table></div>'
      '<div class="sub">Base publi\u00e9e %s \u2192 base normalis\u00e9e %s \u00b7 %s</div>'
      '<div style="margin-top:10px">%s %s</div>'
      '<div class="sub">Multiple exig\u00e9 par le cours pour %s %%/an nets : %s\u00d7 (\u00e0 comparer au multiple central) \u00b7 seconde m\u00e9thode : %s</div></div>' % (
          srows, fr(vv(valo.get('base_publiee')), 2), fr(vv(valo.get('base_normalisee')), 2), esc(valo.get('effet')),
          bdg('Multiple exig\u00e9 : %s' % R.get('mult_exige_lab', 'n.d.'), L_LAB('mult_exige', R.get('mult_exige_lab'))),
          bdg('Part du multiple %s %%' % fr(R.get('part_mult'), 0), R.get('niv_part', 'gris')) if num(R.get('part_mult')) else '',
          fr(R.get('tx'), 1), fr(R.get('mult_exige'), 1), esc(valo.get('seconde_methode') or 'n.d.')))
    # V23.1 : bloc « Robustesse du rendement » retire (demande de Nico, 30/10/2026) ; calculs conserves dans le moteur.

    # ---------------- bloc 4
    S_('plan')
    tl = R.get('taille') or {}
    st_t = tl.get('statut')
    if st_t == 'sans objet':
        t_txt = ('<p>Taille Voie A : <b>sans objet</b> \u2014 l\u2019achat standard est bloqu\u00e9 (voir ce qui rouvrirait la porte, juste au-dessus)%s.</p>'
                 % ('' if (R.get('voie_b') or {}).get('statut') not in ('OUVERTE', 'EN ATTENTE') else ' ; Voie B : %s %% au plus' % fr(VOIE_B_TAILLE, 0)))
    else:
        t_txt = ('<p>%s : <b>%s %%</b> du portefeuille%s \u2014 contrainte active : %s.</p>' % (
            'Plafond conditionnel (seulement si le prix d\'achat est atteint)' if st_t == 'conditionnel' else 'Taille maximale',
            fr(tl.get('max'), 1), ' (provisoire : volume inconnu)' if tl.get('provisoire') else '', esc(tl.get('contrainte'))))
    A('<div class="c"><h3>Taille, tranches et rythme</h3>' + t_txt +
      '<p>Tranches %s \u00b7 tranche 1 %s</p><div>%s</div><div class="sub">Capital pr\u00e9serv\u00e9 au prix maximum d\'achat : %s /100 \u00b7 priorit\u00e9 de suivi : %s</div></div>' % (
          esc(R.get('tranches') or 'n.d.'), esc(R.get('tranche1') or 'n.d.'),
          bdg('Momentum : %s' % (R.get('momentum_lecture') or {}).get('lab', R.get('momentum') or 'n.d.'),
              (R.get('momentum_lecture') or {}).get('lvl', L_LAB('momentum', R.get('momentum')))) +
          ' <span class="sub">%s%s</span>' % (esc((R.get('momentum_lecture') or {}).get('txt', '')),
              ' \u00b7 les tranches 50/25/25 exigent aussi la performance relative 6 mois' if (R.get('momentum') == 'IND\u00c9TERMIN\u00c9' and num((R.get('momentum_lecture') or {}).get('mm'))) else ''),
          fr(R.get('cap_PA'), 0), esc(R.get('priorite') or 'n.d.')))
    lec = D.get('lecture') or {}
    A('<div class="c"><h3>Points forts et points faibles</h3><div class="grid g2">'
      '<ul class="plus">%s</ul><ul class="moins">%s</ul></div></div>' % (
          ''.join('<li>%s</li>' % esc(x) for x in (lec.get('forces') or [])),
          ''.join('<li>%s</li>' % esc(x) for x in (lec.get('faiblesses') or []))))
    pd = lec.get('point_decisif') or {}
    A('<div class="concl"><h3>Conclusion</h3><p>%s</p>'
      '<p><b>Point d\u00e9cisif</b><br>Raison du prix : %s<br>Fondement du d\u00e9saccord : %s<br>'
      'Ce qui nous donnerait tort : %s<br>Marge d\'erreur : %s<br>Pourquoi maintenant : %s</p>'
      '<p>Action : %s</p><p>Invalidation : %s</p><p class="sub">Prochain catalyseur : %s</p>'
      '<p>%s \u2014 %s <span class="sub">(\u00e9ch\u00e9ance %s ; non remplie \u2192 \u274c sans nouvelle analyse)</span></p></div>' % (
          esc(lec.get('these_2p')), esc(pd.get('raison_prix')), esc(pd.get('desaccord')), esc(pd.get('tort')),
          esc(pd.get('marge_erreur') or ''), pm_html(R), esc(lec.get('action')), esc(lec.get('invalidation')),
          esc(lec.get('catalyseur')), bdg(v.get('suivi', 'n.d.'), L_LAB('suivi', v.get('suivi')), 'gros'),
          esc(v.get('suivi_condition')), esc(v.get('suivi_date'))))

    # ligne NICO + annexes
    S_('nico')
    A('<h2>Ligne pour l\'outil de tri</h2><div class="nico">%s</div>' % esc(R['nico']))
    S_('coulisses')
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
    S_('script')
    src = json.dumps(D.get('_source') or {}, ensure_ascii=False).replace('</', '<\\/')
    A('<script type="application/json" id="nico-source" data-version="%s">%s</script>' % (VERSION, src))
    A('</div></body></html>')
    # ---------------- V23.7 : assemblage en episodes
    meta_ = D.get('meta') or {}
    S7, d7 = R.get('sources_g') or {}, R.get('duree') or {}
    acc2 = 'Notre central : %s. Le passé : %s. Les analystes : %s.' % (
        ('%s %%/an de BPA' % fr(R.get('gc'), 1)) if num(R.get('gc')) else 'n.d.',
        ('%s %%/an' % fr(S7.get('passe'), 1)) if num(S7.get('passe')) else 'n.d.',
        ('%s %%/an' % fr(S7.get('consensus'), 1)) if num(S7.get('consensus')) else 'non documentés')
    acc3 = 'Ce qui empêche un concurrent bien financé de prendre clients et profits, et pendant combien d’années.'
    acc4 = ('Si le mauvais scénario arrive, il te reste %s € sur 100 au cours du jour.' % fr(R.get('cap_cours'), 0)
            if num(R.get('cap_cours')) else 'Les risques qui pourraient faire mentir la thèse.')
    acc5 = ('Au cours du jour : %s %%/an pour un seuil de %s %%. Prix maximum d’achat : %s %s.' % (
        fr(R.get('retenu'), 1), fr(R.get('tx'), 1), fprix(R.get('PA')), esc(meta_.get('devise', '')))
        if R.get('calc') else 'Valorisation non exécutée : pas de prix d’achat.')
    acc6 = ('Combien acheter (taille %s), à quel rythme (tranches %s), et ce qui te ferait changer d’avis.' % (taille_txt(R), R.get('tranches') or 'n.d.')
            if (R.get('taille') or {}).get('statut') != 'sans objet' else
            'Pourquoi l’achat standard est bloqué, ce qui rouvrirait la porte, la Voie B, et ce qui te ferait changer d’avis.')

    def T_(*noms):
        return ''.join(''.join(BK.get(n_, [])) for n_ in noms)
    pages = [T_('tete', 'pilote'),
             episode('ÉPISODE 1', 'L’histoire', 'Ce qu’elle fait, le problème qu’elle résout, ce qu’elle apporte au monde, et pourquoi elle pourrait gagner.'),
             T_('ep1'), _sur(monde_html, R),
             episode('ÉPISODE 2', 'La croissance : de combien les bénéfices grandissent', acc2),
             _sur(marche_html, D, R), _sur(croissance_html, D, R, meta_.get('devise', '')),
             ('<details class="c"><summary>📋 Le tableau des chiffres : CA, marge, BPA, FCF par action</summary>%s</details>' % T_('traj')) if BK.get('traj') else '',
             T_('vent'),
             episode('ÉPISODE 3', 'La forteresse : combien de temps ça tient', acc3),
             _sur(duree_html, R), T_('moatdir', 'piliers', 'boule'),
             T_('valeur'),
             episode('ÉPISODE 4', 'Ce qui peut la casser', acc4), T_('registre', 'risq_cartes', 'plancher'),
             episode('ÉPISODE 5', 'Le prix : combien tu gagnes', acc5), T_('prix', 'prix_tri'),
             episode('ÉPISODE 6', 'Le plan', acc6), T_('resultats'), _sur(voie_b_html, D, R), _sur(porte_ouverture_html, D, R),
             T_('plan'), _sur(angles_morts_html, R), T_('nico'),
             '<details class="coul"><summary>🎬 Coulisses — taux exigé, horizon, contrôles, sources et lexique</summary>%s%s</details>' % (T_('coulisses'), lexique_html()),
             T_('script')]
    return ''.join(pages)


# ------------------------------------------------------------------ Fiche de tri, création de valeur et autofinancement
# Trois blocs de LECTURE. Aucun point dans Q, aucun veto, aucun effet sur le taux exige, le prix ou la taille (R3).
L_SPREAD2 = lambda x: cut(x, [0, 2, 4, 8], [2, 3, 4, 5, 6])      # economic spread, pts
L_EVAM = lambda x: cut(x, [0, 5, 10], [2, 3, 4, 5])               # marge EVA, % du CA
L_EVAMO = lambda x: cut(x, [-1, 0, 1], [2, 3, 4, 5])              # EVA momentum, % du CA precedent
SLOAN_MAX, BENEISH_MAX, ALTMAN_MIN, PIOTROSKI_MAX = 0.10, -1.78, 1.81, 3


def est_financier(D):
    """V23.3 : banque ou assureur par qualification EXPLICITE : metrique de rentabilite « (SECTEUR FINANCIER) »
    ou profil.financier = true. Servir des clients financiers ou fournir des terminaux de paiement ne suffit pas."""
    pf = (D.get('profil') or {}) if isinstance(D.get('profil'), dict) else {}
    lab = str(vv((D.get('rentabilite') or {}).get('metrique') if isinstance(D.get('rentabilite'), dict) else '') or '').upper()
    marqueur = 'SECTEUR FINANCIER' in lab
    decl = pf.get('financier')
    if decl is False and marqueur:  # V23.4 : un false ne peut pas annuler la qualification par la metrique
        warn('Qualification financière contradictoire : profil.financier = false mais métrique « %s » \u2014 traitée comme financière.' % lab)
    if decl is True and not marqueur:
        warn('profil.financier = true mais métrique de rentabilité non financière (%s) : aligner la métrique (ROE / ROTE (SECTEUR FINANCIER)).'
             % (lab or 'n.d.'))
    return decl is True or marqueur


def _badge2(x):
    y = (list(x) + ['', ''])[:2] if isinstance(x, list) else [x or '', '']
    return str(y[0] or '').strip(), str(y[1] or '').strip()


def _note_ctrl(D, pilier, i):
    cs = G(D, 'qualite.controles.' + pilier) or []
    try:
        c = cs[i]
        c = c[0] if isinstance(c, list) else c
        return float(c) if num(c) else None
    except (IndexError, TypeError, ValueError):
        return None


def calc_profil(D, R):
    """(A) Fiche de tri : les criteres du tri 10 par 10, visibles dans le dossier complet.
    Ethique contraire et Etat > 50 % = red flags affiches, jamais un blocage (decision de Nico, 30/10/2026)."""
    pr = D.get('profil') if isinstance(D.get('profil'), dict) else {}
    out = {'doc': bool(pr)}
    for k in ('moat', 'recurrence', 'cycle', 'ethique'):
        lab, txt = _badge2(pr.get(k))
        out[k] = {'lab': lab.upper() if lab else 'NON DOCUMENTÉ', 'txt': txt,
                  'lvl': L_LAB(k, lab) if lab else 'gris', 'cle': _cle(lab, k) if lab else None}
    etat = vv(pr.get('etat_pct'))
    out['etat'] = etat
    out['etat_lvl'] = 'gris' if not num(etat) else (5 if etat <= 10 else 3 if etat <= 50 else 1)
    out['etat_txt'] = V(pr.get('etat_pct'))['src'] or V(pr.get('etat_pct'))['note'] or ''
    # forensique : drapeaux du tri (Sloan ajoute), aucune incidence sur la credibilite du baissier
    fo = G(D, 'risques.forensique')
    fo = fo if isinstance(fo, dict) else {}  # V23.2 : champ malforme = n.d.
    z, m, f, s = (vv(fo.get(k)) for k in ('z_altman', 'm_beneish', 'f_piotroski', 'sloan'))
    se = fo.get('sloan_entrees')
    if not num(s) and isinstance(se, dict):
        # V24 : Sloan calcule depuis les comptes deja lus = (resultat net - flux d'exploitation - flux d'investissement) / actifs moyens
        ni, cfo, cfi, ta = (vv(se.get(k)) for k in ('resultat_net', 'cfo', 'cfi', 'actifs_moyens'))
        if all(num(x) for x in (ni, cfo, cfi, ta)) and ta > 0:
            s = (ni - cfo - cfi) / ta
            chk('Sloan calculé depuis les comptes (V24)', 'validé', '(%s − %s − %s) / %s = %s' % (fr(ni, 0), fr(cfo, 0), fr(cfi, 0), fr(ta, 0), fr(s, 3)))
        else:
            warn('risques.forensique.sloan_entrees incomplet : il faut resultat_net, cfo, cfi et actifs_moyens (même unité).')
    if num(s) and abs(s) > 1.5:  # V23.2 : jamais de conversion deduite de la grandeur
        warn('Ratio de Sloan %s : valeur ambiguë (le contrat attend un décimal, 0,10 et non 10) — vérifier l\u2019unité ; '
             'aucune conversion automatique.' % fr(s, 2))
    financier = est_financier(D)  # V23.3 : qualification explicite, plus de detection par le nom du secteur
    # applicabilite : Altman, Beneish et Sloan ne sont pas concus pour les banques et assureurs
    indic = [('Altman Z', z, (lambda v: v < ALTMAN_MIN), '%s < 1,81', 2, not financier),
             ('Beneish M', m, (lambda v: v > BENEISH_MAX), '%s > \u22121,78', 2, not financier),
             ('Sloan', s, (lambda v: v > SLOAN_MAX), '%s > 0,10', 2, not financier),
             ('Piotroski', f, (lambda v: v <= PIOTROSKI_MAX), '%s/9 \u2264 3', 0, True)]
    alertes, mesures, absents, exclus = [], 0, [], []
    for nom, v, test, fmt, d, applicable in indic:
        if not applicable:
            exclus.append(nom)
        elif not num(v):
            absents.append(nom)
        else:
            mesures += 1
            if test(v):
                alertes.append('%s %s' % (nom, fmt % fr(v, d)))
    out['forensique'] = {'z': z, 'm': m, 'f': f, 'sloan': s, 'alertes': alertes, 'mesures': mesures,
                         'absents': absents, 'exclus': exclus, 'financier': financier}
    if len(alertes) >= 2:
        warn('Double alerte forensique (%s) : investigation requise. Dans le tri 10 par 10, ta règle la plafonne en liste 4 ; '
             'aucun effet automatique dans le moteur.' % ' ; '.join(alertes))
    # red flags : signal seulement
    flags = []
    e = out['ethique']
    if e['cle'] == 'CONTRAIRE':
        flags.append((1, '\U0001f6a9 Éthique — contraire à tes valeurs', e['txt'] or 'motif non précisé'))
    elif e['cle'] in ('À TRANCHER', 'A TRANCHER'):
        flags.append((3, '⚠️ Éthique — à trancher', e['txt'] or 'motif non précisé'))
    if num(etat) and etat > 50:
        flags.append((1, '\U0001f6a9 État actionnaire de contrôle (%s %%)' % fr(etat, 0),
                      out['etat_txt'] or 'contrôle public : intérêt de l’État avant celui des minoritaires possible'))
    elif num(etat) and etat > 10:
        flags.append((3, '⚠️ État actionnaire à %s %%' % fr(etat, 0), out['etat_txt']))
    if len(alertes) >= 2:
        flags.append((3, '⚠️ Double alerte forensique', ' · '.join(alertes)))
    R['flags'] = flags
    # coherence avec les controles proprietaires (aucune note modifiee)
    m2, v1 = _note_ctrl(D, 'modele', 1), _note_ctrl(D, 'visibilite', 0)
    km, kr, kc = out['moat']['cle'], out['recurrence']['cle'], out['cycle']['cle']
    if km == 'LARGE' and m2 is not None and m2 < 0.5:
        warn('Moat LARGE déclaré alors que Modèle 2 = 0 (aucun avantage prouvé) : incohérence à résoudre.')
    if km == 'AUCUN' and m2 == 1:
        warn('Moat AUCUN déclaré alors que Modèle 2 = 1 (avantage démontré) : justifier ou corriger.')
    if kr in ('RÉCURRENT', 'RECURRENT') and v1 == 0:
        warn('Revenus déclarés RÉCURRENTS alors que Visibilité 1 = 0 : justifier ou corriger.')
    if kr == 'PONCTUEL' and v1 == 1:
        warn('Revenus déclarés PONCTUELS alors que Visibilité 1 = 1 (contrats ou carnet fiables) : justifier ou corriger.')
    if kc == 'HAUT DE CYCLE':
        bp, bn = vv(G(D, 'valo.base_publiee')), vv(G(D, 'valo.base_normalisee'))
        if num(bp) and num(bn) and bp > 0 and bn >= 0.98 * bp:
            warn('Haut de cycle probable mais base normalisée ≈ base publiée : la base est-elle au sommet ? (§7 : milieu de cycle).')
        anc = G(D, 'valo.scenarios.baissier.ancrage')
        lab_a = str((anc[0] if isinstance(anc, list) and anc else anc) or '').upper()
        if anc and not any(k in lab_a for k in ('MILIEU DE CYCLE', 'PIRE EXERCICE')):
            warn('Haut de cycle probable : le baissier devrait partir du milieu de cycle ou du pire exercice publié.')
    manquants = [nom for nom, k in (('moat', 'moat'), ('récurrence', 'recurrence'), ('cycle', 'cycle'),
                                    ('éthique', 'ethique')) if out[k]['lvl'] == 'gris']
    if not num(etat):
        manquants.append('part de l’État')
    if not num(s):
        manquants.append('Sloan')
    if manquants:
        warn('Fiche de tri incomplète (profil) : %s.' % ', '.join(manquants))
    chk('Fiche de tri (V23)', 'validé' if not manquants else 'n.d.',
        'complète' if not manquants else 'manque : ' + ', '.join(manquants))
    chk('Éthique et État : signal sans blocage (V23)', 'validé',
        ' ; '.join(t for _, t, _ in flags) if flags else 'aucun red flag')
    R['profil'] = out


def calc_valeur(D, R):
    """(B) Creation de valeur. V23.2 : la situation ACTUELLE se classe sur le spread actuel ; moyenne 5 ans et pire
    sur 10 ans restent du contexte. Cas nuls traites a part. Pour les financieres, le spread ROIC - WACC d'Unclestock
    n'est jamais compare a un ROE - cout des fonds propres."""
    cv = D.get('creation_valeur') if isinstance(D.get('creation_valeur'), dict) else {}
    sp, s5, s10, em, emo = (vv(cv.get(k)) for k in ('spread', 'spread_5a', 'spread_pire_10a', 'eva_marge', 'eva_momentum'))
    brut = cv.get('serie')
    if brut is not None and not isinstance(brut, (list, tuple)):
        warn('creation_valeur.serie illisible \u2014 historique absent.')
        brut = []
    serie = [(x[0], vv(x[1])) for x in (brut or [])
             if isinstance(x, (list, tuple)) and len(x) > 1 and num(vv(x[1]))]
    if not any(num(x) for x in (sp, s5, s10, em, emo)) and not serie:
        R['valeur'] = {'doc': False, 'synth': 'NON DOCUMENTÉ', 'lvl': 'gris'}
        warn('Bloc \U0001f48e création de valeur non renseigné (creation_valeur) : à demander dans le même appel Unclestock.')
        chk('Création de valeur (V23)', 'n.d.', 'creation_valeur absent')
        return
    mom = ''
    if num(emo):
        mom = ('Le profit économique augmente ; son origine (capital investi, marges ou coût du capital) est à expliquer.' if emo > 0 else
               'Le profit économique est stable.' if emo == 0 else
               'Le profit économique recule : marge en baisse, capital qui rapporte moins ou coût du capital plus élevé.')
    if num(sp):
        if sp > 0:
            if num(emo) and emo > 0:
                synth, lvl = 'CRÉATION DE VALEUR EN HAUSSE', (6 if (sp >= 8 and emo >= 1) else 5)
            elif num(emo) and emo == 0:
                synth, lvl = 'CRÉE DE LA VALEUR, PROFIT ÉCONOMIQUE STABLE', 5
            elif num(emo):
                synth, lvl = 'CRÉE DE LA VALEUR, MAIS MOINS', 4
            else:
                synth, lvl = 'CRÉE DE LA VALEUR', 4
            txt = 'Aujourd\u2019hui, chaque euro investi rapporte plus qu\u2019il ne coûte. ' + mom
        elif sp == 0:
            synth, lvl = 'AU COÛT DU CAPITAL', 3
            txt = 'Aujourd\u2019hui, le capital rapporte exactement ce qu\u2019il coûte : ni création, ni destruction. ' + mom
        else:
            if num(emo) and emo > 0:
                synth, lvl = 'DÉTRUIT ENCORE, MAIS S\u2019AMÉLIORE', 3
            else:
                synth, lvl = 'DESTRUCTION DE VALEUR', 2
            txt = 'Aujourd\u2019hui, le capital rapporte moins qu\u2019il ne coûte. ' + mom
        if num(s5) and (s5 > 0) != (sp > 0) and s5 != 0 and sp != 0:
            txt += ' La moyenne 5 ans (%s pts) dit l\u2019inverse : changement de régime à expliquer.' % fr(s5, 1, True)
    elif num(s5):
        synth = 'CRÉATION HISTORIQUE \u2014 SITUATION ACTUELLE NON DOCUMENTÉE' if s5 > 0 else (
            'DESTRUCTION HISTORIQUE \u2014 SITUATION ACTUELLE NON DOCUMENTÉE' if s5 < 0 else
            'HISTORIQUE AU COÛT DU CAPITAL \u2014 SITUATION ACTUELLE NON DOCUMENTÉE')
        lvl, txt = 'gris', 'Seule la moyenne sur 5 ans est connue : elle ne dit pas où en est la société aujourd\u2019hui. ' + mom
    else:
        synth, lvl, txt = 'À DOCUMENTER', 'gris', 'Spread actuel non renseigné. ' + mom
    rb = R.get('rentab') or {}
    if rb.get('metrique') == 'ROIC':
        if num(rb.get('med')) and num(rb.get('wacc')) and num(s5):
            d = (rb['med'] - rb['wacc']) - s5
            if abs(d) > 5:
                warn('Spread moyen 5 ans (%s pts) éloigné de la médiane du dossier \u2014 ROIC \u2212 coût du capital (%s pts) : '
                     'définitions différentes (avant/après impôt, WACC). La série du dossier reste la référence des notes.'
                     % (fr(s5, 1, True), fr(rb['med'] - rb['wacc'], 1, True)))
    else:
        warn('Spread Unclestock = ROIC \u2212 WACC ; le dossier mesure la rentabilité en %s : pas de comparaison entre les deux '
             '(pour une financière, la référence est ROE \u2212 coût des fonds propres).' % rb.get('metrique', 'n.d.'))
    pire = ''
    if num(s10):
        pire = ('Au pire de la décennie, le capital rapportait moins qu\u2019il ne coûte : ancrage possible du baissier (PIRE EXERCICE).' if s10 < 0 else
                'Au pire de la décennie, le capital rapportait tout juste son coût.' if s10 == 0 else
                'Même au pire de la décennie, le capital rapportait plus qu\u2019il ne coûte : signe d\u2019un avantage qui résiste au cycle.')
    R['valeur'] = {'doc': True, 'sp': sp, 's5': s5, 's10': s10, 'em': em, 'emo': emo, 'serie': serie,
                   'synth': synth, 'lvl': lvl, 'txt': txt.strip(), 'pire': pire, 'source': V(cv.get('source'))['v'] or
                   V(cv.get('spread'))['src'] or V(cv.get('spread_5a'))['src'] or ''}
    chk('Création de valeur (V23)', 'validé' if lvl != 'gris' else 'n.d.', synth)


def entrees_autofinancement(D):
    """Les anciens dossiers conservent leurs hypothèses au rechargement."""
    champs = D.get('autofinancement')
    if isinstance(champs, dict):
        return champs
    ancien = D.get('triangle')
    return ancien if isinstance(ancien, dict) else {}


def _equiv_nopat(tr):
    """V23.4 : equivalence resultat net / NOPAT documentee = ["OUI", motif] (dette et frais financiers stables...)."""
    e = tr.get('equivalence_nopat')
    lab, motif = _badge2(e) if isinstance(e, (list, str)) else (('OUI', '') if e is True else ('', ''))
    return motif if (lab.upper().startswith('OUI') and motif) else ''


METHODES_FINANCEMENT = {'OPERATIONNELLE': 'OPÉRATIONNELLE', 'OPÉRATIONNELLE': 'OPÉRATIONNELLE',
                'FONDS PROPRES': 'FONDS PROPRES'}


CAPITAL_LEGER = ('LÉGER', 'LÉGER PROBABLE', 'NÉGATIF')
PROTECTIONS = (
    (r'contrats?', 'PAR CONTRATS'),
    (r'marques?', 'PAR LA MARQUE'),
    (r'réseau\w*', 'PAR LE RÉSEAU'),
    (r'réglement\w*|licences?|brevets?|exclusivit\w*', 'PAR UN DROIT'),
    (r'coûts? (?:de changement|de transfert|de migration)', 'PAR LES COÛTS DE CHANGEMENT'),
    (r'données|distribution|intégration|certification', ''),
)
DATE_PREUVE = r'(?<!\d)(?:19|20)\d{2}(?!\d)'


def _chiffre_capital(capital, cle, minimum=None, strict=False):
    # Le nouveau bloc conserve sa provenance et n'altère pas le JSON de calcul.
    try:
        valeur = _en_nombre(vv(capital.get(cle)))
    except (TypeError, ValueError, OverflowError):
        return None
    if valeur is None or (minimum is not None and (valeur < minimum or (strict and valeur == minimum))):
        return None
    return valeur


def _glaciere(brut):
    """Contrôle de forme uniquement : le moteur ne vérifie pas la source elle-même."""
    if not isinstance(brut, list) or len(brut) != 2 or not isinstance(brut[0], str):
        return 'n.d.', '', False, ''
    badge = {'copiable': 'COPIABLE', 'protege': 'PROTÉGÉ'}.get(_sans_accent(brut[0]).strip())
    if badge is None:
        return 'n.d.', '', False, ''
    texte = brut[1].strip() if isinstance(brut[1], str) else ''
    protection, sep, preuve = texte.partition('|')
    nom, motif = '', ''
    for pattern, etiquette in PROTECTIONS:
        if re.search(r'\b(?:' + pattern + r')\b', protection, re.I):
            nom, motif = etiquette, pattern
            break
    if not sep:
        preuve = re.sub(motif, '', texte, flags=re.I) if motif else ''
    elif not motif:
        # Une protection hors liste peut être nommée explicitement avant le séparateur.
        protection = protection.strip()
        if (re.fullmatch(r'(?:(?:protection|moat|avantage)(?: non financi(?:ère|er))?|n\.d\.|à documenter|aucun|inconnu)?', protection, re.I)
                or re.match(r'(?:trésorerie|cash|roic|roe|roa|marge|capital|bilan|dette)\b', protection, re.I)):
            preuve = ''
    documentee = (badge == 'PROTÉGÉ' and bool(re.search(DATE_PREUVE, preuve))
                  and not re.search(r'\b(?:à fournir|à vérifier|à documenter|non documenté)\b', preuve, re.I)
                  and len(re.findall(r'\b[\wÀ-ÿ]+\b', re.sub(DATE_PREUVE, '', preuve))) >= 2)
    return badge, texte, documentee, nom if documentee else ''


def calc_capital(D, R):
    brut = D.get('capital')
    c = brut if isinstance(brut, dict) else {}
    ca = _chiffre_capital(c, 'ca_meur', 0, strict=True)
    investi = _chiffre_capital(c, 'capital_investi_meur')
    origine = str(vv(c.get('origine')) or '').strip().upper()
    if origine not in ('BFR', 'RACHATS') and (investi is None or investi <= 0):
        def_capital = str(vv(c.get('definition')) or '')
        note_capital = str(V(c.get('capital_investi_meur'))['note'] or '')
        description = (def_capital + ' ' + note_capital).lower()
        if 'fonds propres' in description and 'rachat' in description:
            origine = 'RACHATS'
        elif re.search(r'\bbfr\s+négatif\b|avances? clients?\b', description):
            origine = 'BFR'
    if investi is not None and investi <= 0 and origine not in ('BFR', 'RACHATS'):
        # Un zéro ou un nombre signé isolé peut être une sentinelle de données manquantes.
        if not V(c.get('capital_investi_meur'))['src']:
            investi = None
    intensite, rotation, note = 'NON MESURÉ', None, ''
    if origine == 'RACHATS':
        note = ('ROIC non pertinent sur ce dénominateur : les rachats ont réduit les fonds propres. '
                'Reconstituer le capital opérationnel, par exemple immobilisations + BFR.')
    elif investi is not None and investi <= 0:
        intensite = 'NÉGATIF'
        note = ('Capital non positif lié au BFR : vérifier les avances clients et les flux.'
                if origine == 'BFR' else 'Capital non positif : documenter son origine.')
    elif investi is not None and ca is not None:
        rotation = ca / investi
        if num(rotation):
            intensite = 'LOURD' if rotation < 1 else 'NORMAL' if rotation <= 4 else 'LÉGER'
    elif investi is None:
        pb, roe, roa = (_chiffre_capital(c, cle, 0, strict=True) for cle in ('pb', 'roe', 'roa'))
        if not est_financier(D) and (pb is not None and roe is not None and pb > 8 and roe > 50
                                     or roa is not None and roa >= 20):
            intensite = 'LÉGER PROBABLE'
            note = 'Indice indirect fondé sur le P/B et le ROE, ou sur un ROA ≥ 20 %. La rotation reste n.d.'
    if not num(rotation):
        rotation = None

    rb = R['rentab']
    mediane = rb.get('med')
    badge, preuve, documentee, protection = _glaciere(c.get('glaciere'))
    obligatoire = intensite in CAPITAL_LEGER or (num(mediane) and mediane > 50)
    if obligatoire and badge == 'n.d.':
        chk('Test de la glacière', 'alerte', 'test requis : documenter COPIABLE ou PROTÉGÉ')
        warn('Test de la glacière requis (capital léger ou rentabilité > 50 %) : documenter COPIABLE ou PROTÉGÉ.')
    if badge == 'PROTÉGÉ' and not documentee:
        chk('Test de la glacière', 'alerte', 'PROTÉGÉ : nommer une protection non financière et donner un fait daté')
        warn('Glacière PROTÉGÉ sans protection non financière nommée ni fait daté.')
    if badge == 'COPIABLE':
        if G(R, 'profil.moat.lab') == 'LARGE':
            chk('Glacière et moat', 'alerte', 'moat LARGE avec glacière COPIABLE')
            warn('Incohérence : moat LARGE avec glacière COPIABLE.')
        if _note_ctrl(D, 'modele', 1) == 1:
            chk('Glacière et Modèle 2', 'alerte', 'Modèle 2 = 1 avec glacière COPIABLE')
            warn('Incohérence : Modèle 2 = 1 avec glacière COPIABLE.')

    af = entrees_autofinancement(D)
    reinv = vv(af.get('reinvestissement'))
    rendement = vv(af.get('rendement_marginal'))
    if not num(rendement) and origine != 'RACHATS' and rb.get('metrique') in ('ROIC', 'ROCE après impôt'):
        rendement = mediane
    distribution = _chiffre_capital(c, 'distribution_pct', 0)
    machine = 'NON MESURÉE'
    if c and num(reinv):
        if reinv >= 50:
            machine = 'RÉINVESTISSEMENT IMPORTANT'
        elif reinv < 25 and distribution is not None and distribution >= 70:
            machine = 'CASH SURTOUT DISTRIBUÉ'
        elif reinv >= 25 or (reinv < 25 and distribution is not None):
            machine = 'ALLOCATION MIXTE'
    R['capital'] = {
        'doc': bool(c), 'intensite': intensite, 'rotation': rotation, 'ca': ca, 'investi': investi, 'origine': origine,
        'note': note, 'glaciere': badge, 'preuve': preuve, 'glaciere_obligatoire': obligatoire,
        'protection_documentee': documentee, 'protection': protection, 'machine': machine,
        'reinvestissement': reinv if c else None, 'rendement': rendement if c else None, 'distribution': distribution,
    }


def calc_autofinancement(D, R):
    """Compare la croissance prévue à la croissance théorique sur un périmètre identique."""
    tr = entrees_autofinancement(D)
    capital = R.get('capital') or {}
    leger = capital.get('intensite') in CAPITAL_LEGER
    rb = R.get('rentab') or {}
    med = rb.get('med') if num(rb.get('med')) else rb.get('last')
    g = R.get('gc')
    # --- methode de croissance theorique
    meth_brute = _sans_accent(vv(tr.get('methode')) or '').upper()
    methode = METHODES_FINANCEMENT.get(meth_brute) or ('OPÉRATIONNELLE' if 'OPERA' in meth_brute else
                                               'FONDS PROPRES' if 'FONDS' in meth_brute else None)
    roic_non_pertinent = capital.get('origine') == 'RACHATS'
    reinv = vv(tr.get('reinvestissement'))
    marg = vv(tr.get('rendement_marginal'))
    roe = vv(tr.get('roe'))
    metr = rb.get('metrique', 'ROIC')
    if methode == 'FONDS PROPRES':
        taux, taux_src = (roe, 'ROE attendu') if num(roe) else (
            (med, 'ROE médian du dossier') if metr == 'ROE' else (None, ''))
        if not num(taux) and not leger:
            warn('Autofinancement, méthode FONDS PROPRES : renseigner autofinancement.roe (ROE attendu) \u2014 un %s n\u2019en tient pas lieu.' % metr)
    else:
        if methode is None and num(reinv) and not leger:
            warn('Autofinancement : méthode non déclarée (autofinancement.methode) \u2014 lue comme OPÉRATIONNELLE (rendement × réinvestissement net / NOPAT).')
        methode = methode or 'OPÉRATIONNELLE'
        if num(marg):
            taux, taux_src = marg, 'rendement marginal documenté'
        elif num(med) and metr in ('ROIC', 'ROCE après impôt') and not roic_non_pertinent:
            taux, taux_src = med, '%s médian historique (approximation)' % metr
        else:
            taux, taux_src = None, ''
            if num(med) and metr not in ('ROIC', 'ROCE après impôt') and not leger:
                warn('Autofinancement, méthode OPÉRATIONNELLE : la rentabilité du dossier est un %s, jamais utilisé comme rendement '
                     'opérationnel \u2014 renseigner autofinancement.rendement_marginal ou passer en méthode FONDS PROPRES.' % metr)
    # croissance de meme nature que la croissance theorique (NOPAT ou resultat net), jamais le BPA brut
    gc_decl = vv(tr.get('croissance_comparable'))
    var_act = vv(tr.get('variation_actions'))
    nature = 'du NOPAT' if methode == 'OPÉRATIONNELLE' else 'du résultat net'
    if num(gc_decl):
        gcomp, gcomp_src = gc_decl, 'croissance centrale %s déclarée' % nature
    elif num(g) and num(var_act) and methode == 'OPÉRATIONNELLE' and not _equiv_nopat(tr):
        gcomp, gcomp_src = None, ('pont par les actions = croissance du résultat net, pas du NOPAT : documenter '
                                  'autofinancement.equivalence_nopat ou renseigner autofinancement.croissance_comparable (NOPAT)')
    elif num(g) and num(var_act):
        gcomp = ((1 + g / 100.0) * (1 + var_act / 100.0) - 1) * 100.0
        gcomp_src = ('croissance du résultat net déduite du BPA (%s %%/an) et du nombre d\u2019actions (%s %%/an)%s'
                     % (fr(g, 1), fr(var_act, 1, True), (' \u2014 équivalence avec le NOPAT documentée : %s' % _equiv_nopat(tr))
                        if methode == 'OPÉRATIONNELLE' else ''))
    else:
        gcomp, gcomp_src = None, ''
    gmax = None
    chk_lib = 'Croissance compatible avec le réinvestissement'
    if leger:
        af, aflvl = 'NON CONTRAINT PAR LE CAPITAL', 4
        chk(chk_lib, 'n.a.', 'ratio rendement × réinvestissement écarté : examiner les contraintes opérationnelles et le pont du §7')
    elif roic_non_pertinent and (methode == 'FONDS PROPRES' or not num(marg)):
        af, aflvl = 'NON APPLICABLE \u2014 PONT REQUIS', 'gris'
        chk(chk_lib, 'n.a.', 'dénominateur non pertinent après rachats : reconstituer le capital opérationnel')
    elif not num(reinv) or not num(taux):
        af, aflvl = 'NON MESURÉE', 'gris'
        chk(chk_lib, 'n.d.', 'renseigner autofinancement.methode, autofinancement.reinvestissement et le rendement adapté à la méthode')
    elif taux <= 0 or reinv < 0:
        af, aflvl = 'NON APPLICABLE \u2014 PONT REQUIS', 'gris'
        chk(chk_lib, 'n.a.', 'rentabilité ou réinvestissement non positif : seul le pont de financement du §7 tranche')
    else:
        gmax = taux * reinv / 100.0
        if not num(gcomp):
            af, aflvl = 'COMPARAISON NON DOCUMENTÉE', 'gris'
            chk(chk_lib, 'n.d.', 'croissance théorique %s %%/an %s, sans pont vers le BPA : renseigner autofinancement.croissance_comparable '
                'ou autofinancement.variation_actions' % (fr(gmax, 1), nature))
        elif gcomp <= gmax + 1e-6:  # tolerance d'arrondi machine
            af, aflvl = 'COMPATIBLE', 5
        elif gcomp <= gmax + 2 + 1e-6:
            af, aflvl = 'COMPATIBLE À 2 PTS PRÈS', 4
        else:
            af, aflvl = 'À FINANCER', 3
            warn('Croissance centrale %s %s %%/an > croissance théorique compatible %s %%/an (%s %s %% × %s %% %s) : '
                 'il faut dette, dilution, hausse de marge ou rendement marginal supérieur \u2014 vérifier le pont du §5 et du §7.'
                 % (nature, fr(gcomp, 1), fr(gmax, 1), taux_src, fr(taux, 1), fr(reinv, 0),
                    'réinvestis' if methode == 'OPÉRATIONNELLE' else 'retenus'))
        if num(gcomp):
            chk(chk_lib, 'alerte' if af == 'À FINANCER' else 'validé',
                'croissance %s %s %%/an, théorique %s %%/an (%s)' % (nature, fr(gcomp, 1), fr(gmax, 1), methode.lower()))
        if reinv > 100:
            warn('Réinvestissement %s %% : au-delà de 100 %%, la croissance suppose trésorerie accumulée ou financement externe \u2014 '
                 'à montrer dans le pont du §7.' % fr(reinv, 0))
    R['autofinancement'] = {
        'af': af, 'aflvl': aflvl, 'methode': methode, 'nature': nature, 'gmax': gmax,
        'gcomp': gcomp, 'gcomp_src': gcomp_src, 'taux': taux, 'taux_src': taux_src, 'reinv': reinv,
        'reinv_src': V(tr.get('reinvestissement'))['src'] or V(tr.get('reinvestissement'))['note'] or '',
    }


def calc_boule_neige(D, R):
    """V23.6 : preuve de croissance, lecture seule ; jamais un ROIC historique comme preuve future."""
    b = D.get('boule_neige')
    b = b if isinstance(b, dict) else {}
    c, t = R.get('capital') or {}, R.get('autofinancement') or {}
    def preuve(cle, labels):
        x = b.get(cle)
        if not isinstance(x, list) or len(x) != 2 or not all(isinstance(v, str) for v in x):
            return 'INCONNUS', '', False
        lab, txt = x[0].strip().upper(), x[1].strip()
        ok = (lab in labels and bool(re.search(DATE_PREUVE, txt))
              and len(re.findall(r'\b\w+\b', txt)) >= 5
              and not re.search(r'non document|à documenter|à vérifier|à fournir', txt, re.I))
        return lab if lab in labels else 'INCONNUS', txt, ok
    deb, deb_txt, deb_doc = preuve('debouches', ('DÉMONTRÉS', 'PLAUSIBLES', 'LIMITÉS', 'INCONNUS'))
    fin, fin_txt, fin_doc = preuve('financement', ('DÉMONTRÉ', 'PLAUSIBLE', 'INSUFFISANT', 'INCONNU'))
    voie = str(b.get('voie') or '').strip().upper()
    voies = ('RÉINVESTISSEMENT', 'SANS CAPITAL IMPORTANT', 'MIXTE')
    horizon = _chiffre_capital(b, 'horizon_ans', 0, strict=True)
    h = V(b.get('horizon_ans'))
    horizon_doc = (horizon is not None and h['prov'] in ('P', 'C', 'E')
                   and isinstance(h['src'], str) and bool(re.search(DATE_PREUVE, h['src'])))
    tr = entrees_autofinancement(D)
    financier = est_financier(D)
    cle = 'roe' if financier and t.get('methode') == 'FONDS PROPRES' else 'rendement_marginal'
    marginal = _chiffre_capital(tr, cle)
    m = V(tr.get(cle))
    cout = (R.get('rentab') or {}).get('wacc')
    rendement_doc = (num(marginal) and num(cout) and m['prov'] in ('P', 'C', 'E')
                     and isinstance(m['src'], str) and bool(re.search(DATE_PREUVE, m['src'])))
    rendement_ok = rendement_doc and marginal > cout
    scalable_ok = (_note_ctrl(D, 'visibilite', 1) == 1 and _note_ctrl(D, 'cash', 0) == 1)
    g = R.get('gc')
    manque = []
    if voie not in voies: manque.append('Le mécanisme de croissance reste à préciser.')
    if not (deb == 'DÉMONTRÉS' and deb_doc): manque.append('Les débouchés ne sont pas suffisamment étayés.')
    if not (horizon_doc and horizon >= 4): manque.append('La durée des débouchés ne couvre pas quatre ans de façon documentée.')
    if not (fin == 'DÉMONTRÉ' and fin_doc): manque.append('Le financement de la croissance reste à confirmer.')
    if voie in ('RÉINVESTISSEMENT', 'MIXTE') and not rendement_ok:
        manque.append('Le rendement des nouveaux investissements reste à établir au-dessus du coût du capital.')
    if voie in ('SANS CAPITAL IMPORTANT', 'MIXTE') and not scalable_ok:
        manque.append('Les marges et la conversion en cash ne suffisent pas à étayer une croissance peu consommatrice de capital.')
    if c.get('glaciere_obligatoire') and not c.get('protection_documentee'):
        manque.append('La protection du modèle doit être documentée.')
    if c.get('glaciere') == 'COPIABLE': manque.append('Le modèle est facile à copier : la durée de la croissance est fragile.')
    if not num(g) or g < 5: manque.append('La croissance centrale par action ne satisfait pas le repère existant de 5 %/an.')
    if rendement_doc and marginal < cout and voie in ('RÉINVESTISSEMENT', 'MIXTE'):
        lab, lvl, txt = 'CROISSANCE DESTRUCTRICE', 2, 'Les nouveaux euros rapporteraient moins que leur coût. Grossir ne suffit pas.'
    elif deb == 'LIMITÉS' and deb_doc:
        lab, lvl, txt = 'BOULE DE NEIGE LIMITÉE', 3, 'L’activité peut rester très rentable, mais ses possibilités de croissance sont limitées.'
    elif fin == 'INSUFFISANT' and fin_doc:
        lab, lvl, txt = 'BOULE DE NEIGE FRAGILE', 3, 'La croissance prévue ne dispose pas encore du financement nécessaire.'
    elif not manque:
        lab, lvl, txt = 'BOULE DE NEIGE ÉTAYÉE', 5, 'Le mécanisme, les débouchés et le financement soutiennent la croissance prévue sur quatre ans. Cela reste une prévision.'
    elif not b:
        lab, lvl, txt = 'BOULE DE NEIGE À DOCUMENTER', 'gris', 'Un ROIC élevé ne suffit pas. Ce dossier ne documente pas encore les débouchés et leur durée.'
    else:
        lab, lvl, txt = 'BOULE DE NEIGE À CONFIRMER', 4, manque[0]
    R['boule_neige'] = dict(lab=lab, lvl=lvl, txt=txt, voie=voie if voie in voies else 'INCONNUE',
        debouches=deb, debouches_texte=deb_txt, debouches_documentes=deb_doc,
        financement=fin, financement_texte=fin_txt, financement_documente=fin_doc,
        horizon=horizon if horizon_doc else None, marginal=marginal, rendement_documente=rendement_doc,
        limite=str(b.get('limite') or ''), manques=manque)


def _col(l):
    return 'var(--gris)' if l in ('gris', 'doc', None) else 'var(--l%s)' % (5 if l == 6 else l)


def flags_html(R):
    fl = R.get('flags') or []
    if not fl:
        return ''
    pire = min(l for l, _, _ in fl)
    rows = ''.join('<div style="margin:8px 0">%s<div class="sub" style="margin-top:4px">%s</div></div>' % (
        bdg(t, l, 'gros wrap'), esc(x)) for l, t, x in fl)
    return ('<div class="c" style="border:2px solid %s"><h3>Red flags — à toi de trancher</h3>%s'
            '<div class="sub">Signal seulement : aucun effet sur le verdict, le prix, le taux exigé ni la taille. '
            'Tu décides en conscience si tu passes outre.</div></div>') % (_col(pire), rows)


def profil_html(D, R):
    P = R.get('profil') or {}
    if not P:
        return ''
    fo = P.get('forensique') or {}

    def tuile(titre, lab, lvl, txt):
        return ('<div><div class="lab">%s</div><div style="margin-top:6px">%s</div><div class="sub">%s</div></div>'
                % (esc(titre), bdg(lab, lvl, 'wrap'), esc(txt)))
    etat = P.get('etat')
    ial = V(G(D, 'risques.ia'))['v']
    f_txt = 'Altman Z %s · Beneish M %s · Piotroski %s/9 · Sloan %s' % (
        fr(fo.get('z'), 2), fr(fo.get('m'), 2), fr(fo.get('f'), 0), fr(fo.get('sloan'), 2))
    na = len(fo.get('alertes') or [])
    nm = fo.get('mesures', 0)
    f_lab = '%s ALERTE%s SUR %s MESURÉ%s' % (na, 'S' if na > 1 else '', nm, 'S' if nm > 1 else '')
    f_known = nm > 0
    f_cov = []
    if fo.get('absents'):
        f_cov.append('non documentés : ' + ', '.join(fo['absents']))
    if fo.get('exclus'):
        f_cov.append('non applicables au secteur financier : ' + ', '.join(fo['exclus']))
    tiles = [
        tuile('\U0001f3f0 Moat', P['moat']['lab'], P['moat']['lvl'], P['moat']['txt']),
        tuile('\U0001f501 Récurrence des revenus', P['recurrence']['lab'], P['recurrence']['lvl'], P['recurrence']['txt']),
        tuile('\U0001f504 Cycle', P['cycle']['lab'], P['cycle']['lvl'], P['cycle']['txt']),
        tuile('\U0001f916 IA', ial or 'INDÉTERMINÉ', L_LAB('ia', ial), V(G(D, 'risques.ia'))['prov'] or ''),
        tuile('\U0001f331 Éthique', P['ethique']['lab'], P['ethique']['lvl'], P['ethique']['txt']),
        tuile('\U0001f3db️ Part de l’État', ('%s %%' % fr(etat, 0)) if num(etat) else 'n.d.', P.get('etat_lvl', 'gris'),
              P.get('etat_txt') or ''),
        tuile('\U0001f9ea Forensique', f_lab if f_known else 'NON MESURÉ', (3 if na >= 1 else (5 if not fo.get('absents') else 4)) if f_known else 'gris',
              f_txt + ((' — ' + ' ; '.join(fo['alertes'])) if fo.get('alertes') else '') +
              ((' · ' + ' · '.join(f_cov)) if f_cov else '')),
    ]
    return ('<div class="c"><h3>\U0001f9ed Fiche de tri</h3><div class="grid g3">%s</div>'
            '<div class="sub" style="margin-top:12px">Les critères du tri 10 par 10, pour que le dossier complet les voie tous. '
            'Lecture seulement : moat et récurrence se notent dans Modèle 2 et Visibilité 1, le cycle dans la base et le baissier.</div></div>'
            % ''.join(tiles))


def _barres_h(items, unite='pts'):
    """Barres horizontales autour de zero, en SVG (donnees reelles uniquement)."""
    items = [(l, v) for l, v in items if num(v)]
    if not items:
        return ''
    m = max(abs(v) for _, v in items) or 1.0
    m = max(m, 4.0)
    W, x0, h = 360, 180, 30
    H = h * len(items) + 14
    out = ['<svg viewBox="0 0 %d %d" width="100%%" style="max-width:520px;display:block;margin:12px 0" role="img" aria-label="spread">' % (W, H)]
    out.append('<line x1="%d" y1="4" x2="%d" y2="%d" stroke="var(--txt2)" stroke-width="1"/>' % (x0, x0, H - 4))
    for i, (lab, v) in enumerate(items):
        y = 8 + i * h
        w = abs(v) / m * 100
        x = x0 if v >= 0 else x0 - w
        col = 'var(--l5)' if v > 0 else 'var(--l2)'
        out.append('<rect x="%.1f" y="%d" width="%.1f" height="18" rx="3" fill="%s"/>' % (x, y, max(w, 1.5), col))
        out.append('<text x="%d" y="%d" fill="var(--txt2)" font-size="12" font-family="ui-monospace,Menlo,monospace"%s>%s</text>' % (
            (x0 - 108 if v >= 0 else x0 + 8), y + 13, '', esc(lab)))
        out.append('<text x="%.1f" y="%d" fill="var(--txt)" font-size="12" font-family="ui-monospace,Menlo,monospace" text-anchor="%s">%s %s</text>' % (
            (x + w + 4) if v >= 0 else (x - 4), y + 13, 'start' if v >= 0 else 'end', fr(v, 1, True), unite))
    out.append('</svg>')
    return ''.join(out)


def valeur_html(R):
    Vb = R.get('valeur') or {}
    if not Vb.get('doc'):
        return ('<div class="c capital-box"><h3>\U0001f48e Création de valeur</h3><div>%s</div>'
                '<div class="sub">Economic spread et EVA non renseignés dans ce dossier.</div></div>' % bdg('NON DOCUMENTÉ', 'gris'))
    cartes = ''.join([
        carte('Spread actuel', ('%s pts' % fr(Vb.get('sp'), 1, True)) if num(Vb.get('sp')) else 'n.d.', L_SPREAD2(Vb.get('sp')), 'ROIC − coût du capital'),
        carte('Moyenne 5 ans', ('%s pts' % fr(Vb.get('s5'), 1, True)) if num(Vb.get('s5')) else 'n.d.', L_SPREAD2(Vb.get('s5')), 'le rythme de croisière'),
        carte('Pire sur 10 ans', ('%s pts' % fr(Vb.get('s10'), 1, True)) if num(Vb.get('s10')) else 'n.d.', L_SPREAD2(Vb.get('s10')), 'la résistance au cycle'),
        carte('EVA momentum', ('%s %%' % fr(Vb.get('emo'), 1, True)) if num(Vb.get('emo')) else 'n.d.', L_EVAMO(Vb.get('emo')),
              'variation du profit économique / CA · marge EVA %s' % (('%s %%' % fr(Vb.get('em'), 1)) if num(Vb.get('em')) else 'n.d.')),
    ])
    serie = Vb.get('serie') or []
    if serie:
        graph = _barres_h([(str(a), v) for a, v in serie]) + '<div class="sub">Spread annuel publié par la source.</div>'
    else:
        graph = _barres_h([('pire 10 ans', Vb.get('s10')), ('moyenne 5 ans', Vb.get('s5')), ('actuel', Vb.get('sp'))])
    return ('<div class="c capital-box"><h3>\U0001f48e Création de valeur — le profit économique progresse-t-il ?</h3>'
            '<div>%s</div><p style="margin-top:10px">%s</p><div class="grid g4">%s</div>%s<p class="sub">%s</p>'
            '<div class="sub">Le ROIC dit si chaque euro est bien investi ; l’EVA (profit économique = (ROIC − coût du capital) × capital investi) '
            'mesure le profit économique ; sa variation dit s’il progresse. À capital investi, ROIC et coût du capital constants, l’EVA reste stable. '
            'La situation actuelle se lit sur le spread actuel ; moyenne et pire historique sont du contexte. '
            'Lecture seulement : la rentabilité se note dans le pilier Capital. Source : %s.</div></div>') % (
        bdg(Vb.get('synth'), Vb.get('lvl', 'gris'), 'gros wrap'), esc(Vb.get('txt')), cartes, graph, esc(Vb.get('pire')),
        esc(Vb.get('source') or 'non nommée'))


def marche_html(D, R):
    """Lecture qualitative des débouchés, sans score supplémentaire."""
    b = R.get('boule_neige') or {}
    marche = G(D, 'boule_neige.marche')
    marche = marche if isinstance(marche, dict) else {}
    preuves = {
        'DÉMONTRÉS': ('Débouchés étayés', 5),
        'PLAUSIBLES': ('Débouchés plausibles', 4),
        'LIMITÉS': ('Débouchés limités', 3),
    }
    lab, lvl = preuves.get(b.get('debouches'), ('Débouchés à documenter', 'gris')) if b.get('debouches_documentes') else (
        'Débouchés à documenter', 'gris')
    elements = (
        ('Où peut-elle gagner des clients ?', marche.get('accessible')),
        ('Pourquoi elle pourrait les gagner', marche.get('avantage')),
        ('Ce que les faits montrent', b.get('debouches_texte')),
        ('Le principal frein', b.get('limite')),
        ('Le test qui peut trancher', marche.get('test')),
    )
    lignes = ''.join('<div class="snow-proof"><strong>%s</strong><p>%s</p></div>' % (esc(k), esc(v.strip()))
                     for k, v in elements if isinstance(v, str) and v.strip())
    if not lignes:
        lignes = '<p class="sub">Il reste à identifier les clients, segments ou pays que l’entreprise peut atteindre.</p>'
    horizon = '<p class="sub">Horizon estimé à partir des preuves du dossier · environ %s ans.</p>' % fr(b['horizon'], 1) if num(b.get('horizon')) else ''
    return ('<section class="c" id="marche-a-conquerir"><h3>🌍 Lui reste-t-il un marché à conquérir ?</h3>'
            '<div>%s</div><div class="grid g2">%s</div>%s</section>') % (bdg(lab, lvl), lignes, horizon)


def roic_hist_html(D, R):
    """V24 : serie et stabilite de la rentabilite, deplacees dans le bloc boule de neige (un seul bloc ROIC)."""
    rb = R['rentab']
    vals = rb['vals']
    graph = ''
    if vals:
        mx = max(vals + ([rb['wacc']] if num(rb['wacc']) else []))
        graph = '<div class="chart">%s</div><div class="xl">%s</div>' % (
            ''.join('<div style="height:%s%%"></div>' % max(2, 100 * v / mx if mx else 0) for v in vals),
            ''.join('<span>%s</span>' % esc(a) for a in rb['annees']))
    return ('<div class="c capital-box"><h3>Rentabilité historique — %s</h3><div>%s</div>%s'
            '<div class="sub">%s · médiane %s %% · min %s %% · dernière %s %% · %s/%s années &gt; coût du capital %s %% · écart interquartile %s pts · tendance %s (pente %s pts/an, dispersion %s pts)</div>'
            '<p class="sub">%s</p></div>') % (
        esc(rb.get('metrique', 'ROIC')), bdg(rb['lab'], rb['lvl'], 'wrap'), graph, esc(rb.get('metrique', 'ROIC')), fr(rb['med'], 1), fr(rb['min'], 1), fr(rb['last'], 1),
        rb['au_dessus'] if rb['au_dessus'] is not None else 'n.d.', rb['n'], fr(rb['wacc'], 1),
        fr(rb['iqr'], 1), esc(rb.get('tend') or 'n.d.'), fr(rb.get('pente'), 1, True), fr(rb.get('iqr_res'), 1),
        esc(G(D, 'rentabilite.definition')))


def capital_html(D, R):
    """V23.6 : trois questions lisibles ; methode et pedagogie a la demande."""
    c, t, rb = R['capital'], R['autofinancement'], R['rentab']
    if 'boule_neige' not in R:
        calc_boule_neige(D, R)
    b = R['boule_neige']
    leger = c['intensite'] in CAPITAL_LEGER
    med, cout = rb.get('med'), rb.get('wacc')
    ratio_utile = c.get('origine') != 'RACHATS' and c['intensite'] != 'NÉGATIF'
    rentable = num(med) and num(cout) and ratio_utile
    if not ratio_utile:
        rent_lab, rent_lvl = 'ROIC non interprétable', 'gris'
        rent_txt = 'Vérifier les flux et reconstituer le capital opérationnel.'
    elif leger:
        rent_lab, rent_lvl = 'ROIC à relativiser', 4
        rent_txt = 'Peu de capital suffit pour fonctionner. Ce ratio ne mesure pas les possibilités de croissance.'
    elif rentable:
        rent_lab, rent_lvl = ('Au-dessus de son coût', 5) if med > cout else ('Au coût du capital', 4) if med == cout else ('Sous son coût', 2)
        rent_txt = 'Rentabilité historique ; les nouveaux investissements peuvent rapporter autrement.'
    else:
        rent_lab, rent_lvl = 'Rentabilité à documenter', 'gris'
        rent_txt = 'Le rendement et son coût doivent être comparables et documentés.'
    if c['protection_documentee']:
        prot_lab, prot_lvl = 'Protection documentée', 5
        prot_txt = c['protection'] or 'Avantage opérationnel documenté.'
    elif c['glaciere'] == 'COPIABLE':
        prot_lab, prot_lvl = 'Facile à copier', 2
        prot_txt = 'Un concurrent peut reproduire le modèle. La rentabilité peut être fragile.'
    elif ((R.get('profil') or {}).get('moat') or {}).get('cle') in ('LARGE', 'ÉTROIT', 'ETROIT'):
        # V24 : une seule lecture du moat dans tout le dossier -- celle de la fiche de tri quand la glaciere n'est pas requise
        mo = R['profil']['moat']
        prot_lab, prot_lvl = 'Moat %s (fiche de tri)' % mo['lab'].lower(), 5 if mo['cle'] == 'LARGE' else 4
        prot_txt = mo['txt'] or 'Source de l’avantage non précisée.'
    else:
        prot_lab, prot_lvl = 'Protection à documenter', 'gris'
        prot_txt = 'La rentabilité seule ne prouve pas un avantage concurrentiel.'
    croissance = ('%s %%/an' % fr(R.get('gc'), 1)) if num(R.get('gc')) else 'n.d.'
    metrique = rb.get('metrique', 'ROIC')
    mesure = ('%s %%' % fr(med, 1)) if num(med) and ratio_utile else 'n.d.'
    deb_lab = {'DÉMONTRÉS': 'Débouchés étayés', 'PLAUSIBLES': 'Débouchés plausibles', 'LIMITÉS': 'Débouchés limités'}.get(b['debouches'], 'Débouchés à documenter') if b['debouches_documentes'] else 'Débouchés à documenter'
    deb_lvl = {'DÉMONTRÉS': 5, 'PLAUSIBLES': 4, 'LIMITÉS': 3}.get(b['debouches'], 'gris') if b['debouches_documentes'] else 'gris'
    horizon = ('Durée visible estimée : ~%s ans (voir « Combien d’années le prix exige-t-il ? »).' % fr(b['horizon'], 0)) if num(b['horizon']) else 'Durée à documenter.'
    cartes = [
        ('1', 'Est-elle rentable ?', mesure, metrique + ' médian', rent_lab, rent_lvl, rent_txt),
        ('2', 'Les débouchés soutiennent-ils la croissance ?', croissance, 'Croissance prévue par action', deb_lab, deb_lvl, horizon),
        ('3', 'Qu’est-ce qui la protège ?', '', '', prot_lab, prot_lvl, prot_txt),
    ]
    cards = ''.join('<article class="snow-card"><div class="snow-question">%s</div>%s%s<div class="snow-status">%s</div><p>%s</p></article>' % (
        esc(titre), '<div class="snow-number">%s</div>' % esc(valeur) if valeur else '',
        '<div class="snow-caption">%s</div>' % esc(caption) if caption else '',
        bdg(lab, lvl, 'wrap'), esc(txt)) for _, titre, valeur, caption, lab, lvl, txt in cartes)
    allocation_txt = {
        'RÉINVESTISSEMENT IMPORTANT': 'Une part importante des profits est réinvestie. Il faut encore vérifier ce qu’elle rapportera.',
        'CASH SURTOUT DISTRIBUÉ': 'Le cash va surtout aux dividendes et aux rachats. Cela n’empêche pas une croissance peu coûteuse en capital.',
        'ALLOCATION MIXTE': 'Les profits servent à la fois à investir et à rémunérer les actionnaires.',
    }.get(c['machine'], 'L’utilisation des profits reste à documenter.')
    mc, objectif = R.get('tri_mult_constant'), R.get('tx')
    prix_lvl = (5 if mc >= objectif else 3) if num(mc) and num(objectif) else 'gris'
    prix_txt = ('%s %%/an net estimé' % fr(mc, 1)) if num(mc) else 'Rendement non calculé'
    prix_note = ('Objectif de la ligne : %s %%/an net.' % fr(objectif, 1)) if num(objectif) else 'Objectif non documenté.'
    prix_note += ' Trajectoire centrale, avec dividendes et fiscalité du dossier. Les rachats sont déjà dans la croissance par action.'
    preuves = [('Mécanisme', b['voie']), ('Débouchés', b['debouches_texte'] or 'Non documentés.'),
        ('Financement', b['financement_texte'] or 'Non documenté.'),
        ('Ce qui limite la croissance', b['limite'] or 'Limite non documentée.'),
        ('Protection', c.get('preuve') or (((R.get('profil') or {}).get('moat') or {}).get('txt')) or 'Non documentée.')]
    preuves_html = ''.join('<div class="snow-proof"><strong>%s</strong><p>%s</p></div>' % (esc(k), esc(v)) for k, v in preuves)
    if b['manques']:
        preuves_html += '<div class="snow-missing"><strong>Ce qui manque pour conclure</strong><ul>%s</ul></div>' % ''.join('<li>%s</li>' % esc(s) for s in b['manques'])
    technique = ('<div class="scroll"><table><tr><th>Coût du capital</th><td>%s %%</td></tr>'
        '<tr><th>Capital nécessaire</th><td>%s · rotation %s</td></tr>'
        '<tr><th>Réinvestissement / rendement retenu / distribution</th><td>%s / %s / %s</td></tr>'
        '<tr><th>Autofinancement de la croissance</th><td>%s</td></tr>'
        '<tr><th>Capital investi</th><td>%s</td></tr><tr><th>Définition</th><td>%s</td></tr></table></div>' % (
            fr(cout, 1), esc(c['intensite']), fr(c['rotation'], 1),
            *(('%s %%' % fr(c[k], 1)) if num(c[k]) else 'n.d.' for k in ('reinvestissement', 'rendement', 'distribution')),
            bdg(t['af'], t['aflvl']), qual_texte(G(D, 'capital.capital_investi_meur')), qual_texte(G(D, 'capital.definition'))))
    if num(t.get('gmax')):
        technique += '<p class="sub">%s · croissance théorique %s %s %%/an · croissance comparable %s %%/an.</p>' % (
            esc(t['methode']), esc(t['nature']), fr(t['gmax'], 1), fr(t['gcomp'], 1))
        if t.get('gcomp_src'):
            technique += '<p class="sub">%s</p>' % esc(t['gcomp_src'])
    if c.get('note'):
        technique += '<p class="sub">%s</p>' % esc(c['note'])
    technique += '<p class="sub">Le test d’autofinancement suppose un rendement constant. Le pont de financement (§7) et les preuves de débouchés complètent ce calcul.</p>'
    # V24 : un seul bloc ROIC -- serie, stabilite et machine a profit reunies ici (le bloc « Rentabilite historique » est retire)
    technique += roic_hist_html(D, R)
    technique += encadres_qualite(D, R)
    return ('<section class="c capital-box snow-box" id="roic-pertinent"><div class="snow-head">'
        '<div><div class="snow-eyebrow">RENTABILITÉ · CROISSANCE · PROTECTION</div><h3>❄️ La boule de neige</h3></div>'
        '%s</div><p class="snow-intro">%s</p><div class="snow-grid">%s</div>'
        '%s%s'
        '<details><summary>Pourquoi cette conclusion ?</summary>%s</details>'
        '<details><summary>Chiffres, historique et sources</summary>%s</details>'
        '<details><summary>Comprendre le ROIC : l’exemple de la glacière</summary>'
        '<p>Une machine de 1 000 € rapporte 200 €/an : rendement de 20 %%. Une glacière de 50 € rapporte 50 €/an : rendement de 100 %%.</p>'
        '<p><strong>Mais peut-on vendre dix fois plus ?</strong> Sans nouveaux clients, le rendement de 100 %% ne fait pas grandir les profits. Il faut aussi un modèle protégé des concurrents.</p></details>'
        '<p class="snow-footnote">Une rentabilité élevée ne garantit pas une hausse du cours. Ce bloc résume les preuves ; le verdict d’achat dépend aussi de la qualité, du prix et des contrôles du dossier.</p></section>') % (
            bdg(b['lab'], b['lvl'], 'wrap'), esc(b['txt']), cards,
            ('<div class="snow-row"><strong>Où va l’argent ?</strong><div>%s<p>%s</p></div></div>' % (
                bdg(c['machine'], 'gris', 'wrap'), esc(allocation_txt))) if c['machine'] != 'NON MESURÉE' else '',
            ('<div class="snow-row"><strong>À ce prix, sans hausse du multiple</strong><div>%s<p>%s</p></div></div>' % (
                bdg(prix_txt, prix_lvl, 'wrap'), esc(prix_note))) if num(mc) else '',
            preuves_html, technique)


# ------------------------------------------------------------------ ligne NICO
STATUTS = {'PF', 'WL', 'SURV', 'SPEC', 'OUT', 'TODO'}


def statut_suivi(D, R):
    """V22.5.1 : statut codifie d'abord ; sinon libelle, du plus restrictif au plus permissif."""
    meta = D.get('meta') or {}; v = D.get('verdict') or {}
    s = str(v.get('suivi') or '').upper()
    ach = str(R.get('verdict_final') or v.get('achat') or '').upper()
    if meta.get('detenue') or R.get('detenue'):
        return 'PF'  # V25.1 : le statut TRI suit la meme decision de detention que le dossier (registre compris)
    code = str(v.get('statut') or '').strip().upper()
    if code in STATUTS:
        return code
    if 'RETIRER' in s or '\u274c' in s or 'REJET' in ach or 'P\u00c9RIM\u00c8TRE' in ach:
        return 'OUT'
    if 'SP\u00c9CULATIVE' in s or 'SPECULATIVE' in s or '\u26a0' in s:
        return 'SPEC'
    if 'SURVEILLANCE' in s or '\U0001f7e1' in s:
        return 'SURV'
    if 'CONSERVER' in s or '\u2705' in s:
        return 'WL'
    warn('D\u00e9cision de suivi non reconnue (%s) : statut TODO dans la ligne NICO.' % (v.get('suivi') or 'absente'))
    return 'TODO'


import unicodedata


def _sans_accent(t):
    return ''.join(c for c in unicodedata.normalize('NFD', str(t or '')) if unicodedata.category(c) != 'Mn').lower()


# (mots-cles de la place, suffixe) : du plus specifique au plus general. '' = cotation americaine, sans suffixe.
PLACES = [
    (('first north stockholm', 'nasdaq stockholm', 'stockholm'), '.ST'), (('copenhague', 'copenhagen'), '.CO'),
    (('helsinki',), '.HE'), (('oslo',), '.OL'), (('bruxelles', 'brussels'), '.BR'), (('paris',), '.PA'),
    (('amsterdam',), '.AS'), (('lisbonne', 'lisbon'), '.LS'), (('milan', 'borsa italiana'), '.MI'),
    (('madrid', 'bme'), '.MC'), (('xetra', 'francfort', 'frankfurt'), '.DE'),
    (('london', 'londres', 'lse', 'aim'), '.L'), (('six', 'zurich', 'swiss'), '.SW'),
    (('vienne', 'vienna', 'wiener'), '.VI'), (('varsovie', 'warsaw', 'gpw'), '.WA'), (('tokyo', 'tse'), '.T'),
    (('hong kong', 'hkex'), '.HK'), (('asx', 'australi'), '.AX'), (('tsxv', 'tsx venture', 'tsx-v'), '.V'),
    (('tsx', 'toronto'), '.TO'), (('nzx',), '.NZ'), (('singapore', 'sgx'), '.SI'),
    (('shanghai',), '.SS'), (('shenzhen',), '.SZ'), (('nasdaq', 'nyse', 'amex', 'otc'), ''),
]


def ticker_normalise(D, R):
    """V22.5.1 : le ticker de la ligne NICO porte le suffixe de place. Complete seulement si la place
    est identifiee sans ambiguite ; sinon alerte. Le ticker saisi reste affiche."""
    meta = D.get('meta') or {}
    t0 = str(meta.get('ticker') or '').strip()
    t = ticker_avec_place(t0)  # V25.1 : « HKEX:327 » -> « 0327.HK »
    b = _sans_accent(meta.get('bourse'))
    suf = None
    for mots, sx in PLACES:
        if any(re.search(r'(^|[^a-z])' + re.escape(m) + r'($|[^a-z])', b) for m in mots):
            suf = sx
            break
    R['ticker_saisi'] = t0
    if t != t0:
        chk('Ticker avec place convertie', 'validé', '%s → %s' % (t0, t))
    if not t:
        R['ticker'] = t
        return t
    if '.' in t:
        if suf and not t.upper().endswith(suf.upper()):
            warn('Ticker %s : suffixe diff\u00e9rent de celui attendu pour %s (%s) \u2014 v\u00e9rifier.' % (t, meta.get('bourse'), suf))
            chk('Ticker avec suffixe de place', '\u00e9chec', '%s attendu' % suf)
        else:
            chk('Ticker avec suffixe de place', 'valid\u00e9', t)
        R['ticker'] = t
    elif suf is None:
        warn('Ticker %s sans suffixe et place \u00ab %s \u00bb non reconnue sans ambigu\u00eft\u00e9 : '
             'ajouter le suffixe \u00e0 la main (ex. FRP.L).' % (t, meta.get('bourse') or 'absente'))
        chk('Ticker avec suffixe de place', '\u00e9chec', 'place ambigu\u00eb ou absente')
        R['ticker'] = t
    else:
        R['ticker'] = t + suf
        chk('Ticker avec suffixe de place', 'valid\u00e9',
            ('compl\u00e9t\u00e9 : %s \u2192 %s' % (t, R['ticker'])) if suf else 'cotation am\u00e9ricaine, sans suffixe')
    return R['ticker']


def ligne_nico(D, R):
    meta = D.get('meta') or {}
    v = D.get('verdict') or {}
    st = statut_suivi(D, R)
    note = (v.get('nico_note') or v.get('suivi_condition') or '').replace('|', '/')
    B = R.get('voie_b') or {}  # V24 : la Voie B remonte dans l'outil de tri, en tete de la note (17 champs inchanges)
    A = R.get('action') or {}
    act = A.get('act', '')
    prix_valides = not A.get('dossier_a_corriger')
    pre = ''
    if act.startswith(('SORTIR', 'VENDRE', 'ALLÉGER')):  # V25.1 : la meme consigne que le dossier ; une vente prime
        pre = '🧭 %s' % act
    elif A.get('plan_tactique') or act in ('DOSSIER À CORRIGER', 'VÉRIFIER LE REGISTRE'):
        pre = '🧭 %s' % act
        if A.get('plan_tactique'):
            pre += ' · ' + A['plan_tactique'].replace('|', '/')
    elif act in ('ACHAT TACTIQUE (VOIE B)', 'RENFORCER TACTIQUEMENT (VOIE B)') and B.get('statut') == 'OUVERTE':
        pre = '🎯 VOIE B OUVERTE ≤ %s obj %s stop %s' % (fprix(B.get('plafond')), fprix(B.get('vp')), B.get('sortie_temps') or 'n.d.')
    elif B.get('statut') == 'EN ATTENTE' and num(B.get('declencheur')) and 'taille tactique' not in str((R.get('action') or {}).get('voie_b') or ''):
        pre = '🎯 VOIE B si > %s puis relancer (≤ %s)' % (fprix(B['declencheur']), fprix(B.get('plafond')))
    elif B.get('statut') == 'HORS ZONE' and num(B.get('declencheur')):
        pre = '🎯 VOIE B hors zone : relancer si > %s' % fprix(B['declencheur'])
    if pre:
        note = ('%s — %s' % (pre, note)) if note else pre
    rouges = [t for l, t, _ in (R.get('flags') or []) if l == 1]  # V23 : red flags visibles dans l'outil de tri
    if rouges:
        court = ' + '.join('ÉTAT >50 %' if 'État' in t else 'ÉTHIQUE' for t in rouges)
        note = ('\U0001f6a9 %s — %s' % (court, note)) if note else '\U0001f6a9 %s' % court
    ch = ['NICO', R.get('ticker') or meta.get('ticker', ''), meta.get('societe', ''), meta.get('devise', ''), st,
          fprix(R.get('PA') if prix_valides else None), fprix(None if A.get('cours_invalide') else vv(meta.get('cours'))),
          fr(R.get('tx'), 1), fr(R.get('retenu') if prix_valides else None, 1),
          fr(R.get('cap_cours') if prix_valides else None, 0), fr(R['q']['Q'], 0), v.get('suivi_date', ''), meta.get('date_eval', ''),
          meta.get('secteur', ''), meta.get('pays', ''), note]
    bl = (R.get('baissier') or {}).get('lab')
    ch.append('BAISSIER ' + (bl or 'N.D.'))  # V25.1 : 17 champs, meme sur un dossier arrete tot
    return ' | '.join(str(c).replace('\u202f', '') for c in ch)


AVENIR_SYNTH = {
    ('EN HAUSSE', 'CAPTÉE'): ('VENT PORTEUR CAPTÉ', 6, 'Le besoin grandit et la société garde la valeur : la demande travaille pour l\'actionnaire.'),
    ('EN HAUSSE', 'PARTAGÉE'): ('VENT PORTEUR PARTAGÉ', 5, 'Le besoin grandit ; la valeur se partage entre acteurs rationnels.'),
    ('EN HAUSSE', 'DISPUTÉE'): ('DEMANDE PORTEUSE, MARGES DISPUTÉES', 3, 'Le besoin grandit, mais la concurrence peut absorber la croissance dans les prix.'),
    ('EN HAUSSE', 'PERDUE'): ('PIÈGE DE CROISSANCE', 2, 'Besoin croissant, profits captés par d\'autres : la demande ne garantit pas le résultat par action.'),
    ('STABLE', 'CAPTÉE'): ('RENTE DURABLE', 5, 'Besoin stable et valeur gardée : rendement par les flux plutôt que par le volume.'),
    ('STABLE', 'PARTAGÉE'): ('BESOIN STABLE', 4, 'Besoin durable, croissance à aller chercher dans les parts de marché ou le prix.'),
    ('STABLE', 'DISPUTÉE'): ('BESOIN STABLE, MARGES DISPUTÉES', 3, 'Le besoin reste, la marge est l\'enjeu.'),
    ('STABLE', 'PERDUE'): ('COMMODITÉ', 2, 'Besoin durable mais banalisé : la valeur part vers les clients ou les concurrents.'),
    ('EN BAISSE', 'CAPTÉE'): ('RENTE QUI S\'ÉRODE', 3, 'La société garde la valeur d\'un besoin qui rétrécit : rendement possible, croissance non.'),
    ('EN BAISSE', 'PARTAGÉE'): ('RENTE QUI S\'ÉRODE', 3, 'Besoin en repli partagé entre acteurs : volumes sous pression.'),
    ('EN BAISSE', 'DISPUTÉE'): ('DÉCLIN', 2, 'Besoin en repli et concurrence pour ce qui reste.'),
    ('EN BAISSE', 'PERDUE'): ('DÉCLIN', 2, 'Besoin en repli et valeur captée par d\'autres.'),
}


def _cle(lab, fam):
    u = str(lab or '').upper()
    for k in sorted(FAM[fam], key=len, reverse=True):
        if k in u:
            return k
    return None


def calc_avenir(D, R):
    """Rubrique V22.8 : le probleme existera-t-il encore, et la societe en gardera-t-elle la valeur ?
    Lecture seulement : aucun point, aucun veto, aucun effet sur le prix (R3). Les faits se notent
    dans Modele 2 (moat) et Modele 3 (durabilite) ; le moteur signale les incoherences."""
    av = G(D, 'acte0.avenir')
    if not isinstance(av, dict):
        R['avenir'] = {'doc': False, 'synth': 'NON DOCUMENTÉ', 'lvl': 'gris', 'txt': ''}
        warn('Rubrique \U0001f52e « le problème existera-t-il encore ? » non renseignée (acte0.avenir).')
        chk('Problème de demain', 'n.d.', 'acte0.avenir absent')
        return
    ex = av.get('existera'); ca = av.get('captation')
    ex = (list(ex) + ['', ''])[:2] if isinstance(ex, list) else [ex or '', '']
    ca = (list(ca) + ['', ''])[:2] if isinstance(ca, list) else [ca or '', '']
    k_ex, k_ca = _cle(ex[0], 'avenir'), _cle(ca[0], 'captation')
    if k_ex in (None, 'NON DOCUMENTÉ', 'INDÉTERMINÉ'):
        synth, lvl, txt = 'À DOCUMENTER', 'gris', 'Le devenir du besoin n\'est pas établi.'
    elif k_ex == 'NON':
        synth, lvl, txt = 'BESOIN EN VOIE DE DISPARITION', 1, 'Le problème résolu disparaît : aucune trajectoire de croissance ne peut s\'appuyer dessus.'
    elif k_ca in (None, 'NON DOCUMENTÉ', 'INDÉTERMINÉ'):
        synth, lvl, txt = 'CAPTATION À DOCUMENTER', 'gris', 'Le besoin est qualifié, mais pas la part de valeur que la société en gardera.'
    else:
        synth, lvl, txt = AVENIR_SYNTH[(k_ex, k_ca)]
    R['avenir'] = {'doc': True, 'probleme': av.get('probleme') or '', 'ex': ex[0] or 'n.d.', 'ex_txt': ex[1],
                   'ex_lvl': L_LAB('avenir', ex[0]), 'ca': ca[0] or 'n.d.', 'ca_txt': ca[1],
                   'ca_lvl': L_LAB('captation', ca[0]) if k_ex != 'NON' else 'gris',
                   'synth': synth, 'lvl': lvl, 'txt': txt}
    # coherence avec les controles proprietaires (aucune note modifiee)
    mod = G(D, 'qualite.controles.modele') or []
    def note(i):
        try:
            return float(mod[i][0]) if isinstance(mod[i], list) else float(mod[i])
        except Exception:
            return None
    m2, m3 = note(1), note(2)
    if k_ex in ('NON', 'EN BAISSE') and m3 == 1:
        warn('Modèle 3 noté 1 (utilité durable) alors que le besoin est %s : justifier ou corriger.' % ('en voie de disparition' if k_ex == 'NON' else 'en baisse'))
    if k_ca == 'PERDUE' and m2 == 1:
        warn('Modèle 2 noté 1 (avantage démontré) alors que la valeur est captée par d\'autres : justifier ou corriger.')
    if k_ca == 'CAPTÉE' and m2 is not None and m2 < 0.5:
        warn('Valeur déclarée CAPTÉE alors que Modèle 2 = 0 (aucun avantage) : incohérence à résoudre.')
    if not str(ex[1]).strip() or (k_ex != 'NON' and not str(ca[1]).strip()):
        warn('Rubrique \U0001f52e : badge sans justification — écrire le pourquoi à côté de chaque badge.')
    chk('Problème de demain', 'validé' if lvl != 'gris' else 'n.d.', synth)


def calc_pourquoi(D, R):
    """Pourquoi maintenant (V22.5) : l'analyste fournit le catalyseur ; le moteur
    qualifie l'absence d'apres la part du multiple. Aucun point, aucun veto, aucun
    effet sur le prix (R3) : seul le rythme des tranches change."""
    pm = G(D, 'lecture.pourquoi_maintenant')
    y = (list(pm) + ['', '', ''])[:3] if isinstance(pm, list) else [pm or '', '', '']
    lab, fait, date = str(y[0] or '').strip().upper(), str(y[1] or '').strip(), str(y[2] or '').strip()
    part = R.get('part_mult')
    if 'DAT' in lab and 'CATALYSEUR' in lab:
        eff = 'CATALYSEUR DAT\u00c9' if (fait and date) else 'CATALYSEUR PROBABLE'
        if eff != 'CATALYSEUR DAT\u00c9':
            warn('Catalyseur d\u00e9clar\u00e9 dat\u00e9 sans fait ou sans date : ramen\u00e9 \u00e0 CATALYSEUR PROBABLE.')
    elif 'PROBABLE' in lab:
        eff = 'CATALYSEUR PROBABLE'
    elif pm is None:
        eff = 'NON DOCUMENT\u00c9'
    elif num(part):
        eff = 'AUCUN \u2014 PARI DE REVALORISATION' if part > 25 else 'AUCUN \u2014 RENDEMENT PAR LES FLUX'
    else:
        eff = 'NON DOCUMENT\u00c9'
    R['pm'] = {'lab': eff, 'fait': fait, 'date': date, 'lvl': L_LAB('pm', eff)}
    if num(part) and part > 25 and eff != 'CATALYSEUR DAT\u00c9' and R.get('tranches'):
        R['tranches'] = '25 / 25 / 50 %'
        R['tranche1'] = ('part du multiple %s %% sans catalyseur dat\u00e9 : la derni\u00e8re moiti\u00e9 attend le catalyseur '
                         'ou un cours au prix de renforcement' % fr(part, 0))
    chk('Pourquoi maintenant', 'valid\u00e9' if eff != 'NON DOCUMENT\u00c9' else 'n.d.', eff)


def pm_html(R):
    pm = R.get('pm') or {}
    if not pm:
        return 'n.d.'
    return bdg(pm['lab'], pm['lvl']) + (' ' + esc(pm['fait']) if pm.get('fait') else '') + \
        (' (%s)' % esc(pm['date']) if pm.get('date') else '')


def taille_txt(R):
    tl = R.get('taille') or {}
    if tl.get('statut') == 'sans objet' or not num(tl.get('max')):
        return 'sans objet' if tl.get('statut') == 'sans objet' else 'n.d.'
    return '%s %s %%' % ('plafond conditionnel' if tl.get('statut') == 'conditionnel' else 'max', fr(tl['max'], 1))


def resume(D, R):
    meta = D.get('meta') or {}; v = D.get('verdict') or {}
    L = ['\U0001f4c4 %s (%s) \u2014 %s' % (meta.get('societe'), R.get('ticker') or meta.get('ticker'), meta.get('date_eval')),
         'Verdict : %s%s' % (R.get('verdict_final') or v.get('achat') or 'n.d.', (' \u2014 ' + v['phrase']) if v.get('phrase') else ''),
         'Q %s %% (couverture %s %%) \u00b7 C %s %% \u00b7 croissance centrale %s %%/an' % (
             fr(R['q']['Q'], 0), fr(R['q']['cov'], 0), fr(R.get('C'), 0), fr(R.get('gc'), 1)),
         'Taux exig\u00e9 %s %%/an \u00b7 rendement retenu %s %%/an \u00b7 prix max. d\'achat %s \u00b7 capital pr\u00e9serv\u00e9 %s/100' % (
             fr(R.get('tx'), 1), fr(R.get('retenu'), 1), fprix(R.get('PA')), fr(R.get('cap_cours'), 0)),
         'Central vs historique %s pts \u00b7 sensibilit\u00e9 du prix %s \u00b7 taille %s \u00b7 tranches %s' % (
             fr(R.get('ecart_hist'), 1, True),
             ('\u2212' + fr(R['tolerance'], 0) + ' %') if num(R.get('tolerance')) else 'n.d.', taille_txt(R),
             R.get('tranches') or 'n.d.'),
         'Rentabilit\u00e9 : %s %s \u00b7 pourquoi maintenant : %s' % ((R.get('rentab') or {}).get('lab'),
             '(tendance %s)' % (R.get('rentab') or {}).get('tend') if (R.get('rentab') or {}).get('tend') else '',
             (R.get('pm') or {}).get('lab', 'n.d.')),
         'Suivi : %s \u2014 %s (%s) \u00b7 priorit\u00e9 %s' % (v.get('suivi') or 'n.d.', v.get('suivi_condition') or 'n.d.',
                                                               v.get('suivi_date') or 'n.d.', R.get('priorite') or 'n.d.')]
    L.insert(2, 'Portes : ' + portes_txt(R))
    avr = R.get('avenir') or {}
    _I = R.get('init') or {}
    L.insert(3, '\U0001f454 Initi\u00e9s : %s%s' % (_I.get('lab') or 'NON V\u00c9RIFI\u00c9', (
        ' \u2014 achats 12 mois %s (%s %% de la capi., %s acheteur(s)) \u00b7 ventes %s \u00b7 %s' % (
            _meur(_I.get('a12')), fr(_I.get('pct_a'), 2), _I.get('nb_ach', 0), _meur(_I.get('v12')), _I.get('effet')))
        if 'a12' in _I else ''))
    L.insert(4, '\U0001f52e Avenir : besoin %s \u00b7 valeur %s \u2192 %s' % (
        avr.get('ex', 'n.d.'), avr.get('ca', 'n.d.'), avr.get('synth', 'NON DOCUMENT\u00c9')))
    if R.get('calc'):
        L.insert(6, 'Plancher : capital pr\u00e9serv\u00e9 %s/100 au cours, %s au prix max. d\'achat \u00b7 prix max. sous la r\u00e8gle \u221240 %% %s%s \u00b7 baissier %s%s%s' % (
            fr(R.get('cap_cours'), 0), fr(R.get('cap_PA'), 0), fprix(R.get('P60')),
            ' (limite le prix d\'achat)' if R.get('plancher_limite') else '',
            (R.get('baissier') or {}).get('lab', 'n.d.'),
            ' \u00b7 plancher prouv\u00e9 \u22121 pt' if R.get('B_actif') else '',
            ' \u00b7 \U0001f3f0 forteresse' if R.get('forteresse') else ''))
    # V23 : red flags juste sous le verdict, puis fiche de tri et création de valeur
    fl = R.get('flags') or []
    if fl:
        L.insert(2, '\U0001f6a9 Red flags (aucun blocage, \u00e0 toi de trancher) : ' + ' \u00b7 '.join(
            '%s%s' % (t, (' \u2014 ' + x) if x else '') for _, t, x in fl))
    P = R.get('profil') or {}
    if P:
        fo = P.get('forensique') or {}
        L.append('\U0001f9ed Fiche de tri : moat %s \u00b7 r\u00e9currence %s \u00b7 cycle %s \u00b7 \u00e9thique %s \u00b7 \u00c9tat %s \u00b7 forensique %s' % (
            P['moat']['lab'], P['recurrence']['lab'], P['cycle']['lab'], P['ethique']['lab'],
            ('%s %%' % fr(P.get('etat'), 0)) if num(P.get('etat')) else 'n.d.',
            ('%s alerte(s) sur %s mesuré(s)%s%s%s' % (len(fo.get('alertes') or []), fo.get('mesures', 0),
                (' : ' + ' ; '.join(fo['alertes'])) if fo.get('alertes') else '',
                (' · non documentés : ' + ', '.join(fo['absents'])) if fo.get('absents') else '',
                (' · non applicables (financière) : ' + ', '.join(fo['exclus'])) if fo.get('exclus') else ''))))
    Vb = R.get('valeur') or {}
    if Vb.get('doc'):
        L.append('\U0001f48e Cr\u00e9ation de valeur : spread %s / 5 ans %s / pire 10 ans %s pts \u00b7 marge EVA %s %% \u00b7 EVA momentum %s %% \u2192 %s' % (
            fr(Vb.get('sp'), 1, True), fr(Vb.get('s5'), 1, True), fr(Vb.get('s10'), 1, True),
            fr(Vb.get('em'), 1), fr(Vb.get('emo'), 1, True), Vb.get('synth')))
    else:
        L.append('\U0001f48e Cr\u00e9ation de valeur : NON DOCUMENT\u00c9E')
    c = R['capital']
    L.append('⚖️ Capital : %s (rotation %s) · protection %s · %s' % (
        c['intensite'], fr(c['rotation'], 1), ' '.join(filter(None, (c['glaciere'], c['protection']))), c['machine']))
    b = R.get('boule_neige')
    if b:
        L.append('❄️ %s — %s' % (b['lab'], b['txt']))
    S7, d7 = R.get('sources_g') or {}, R.get('duree') or {}
    _pa = lambda x: ('%s %%/an' % fr(x, 1)) if num(x) else 'n.d.'
    _du = lambda t: ('~%s ans' % fr(t, 0)) if num(t) else 'n.d.'
    _q7 = (R.get('q') or {}).get('Q')
    _l7 = R.get('longevite') or {}
    _fl, _fp = _pilier_faible(R)
    L.insert(2, '🎯 Qualité %s (%s%s) ➜ rendement net estimé %s (seuil %s %%) ➜ bénéfices %s (passé %s · analystes %s → %s) ➜ '
             'longévité %s : le prix exige %s de croissance, on en voit %s (preuves %s)' % (
        ('%s %%' % fr(_q7, 0)) if num(_q7) else 'n.d.', lab_qualite(_q7)[0], (' · point faible %s %s %%' % (_fl.lower(), fr(_fp, 0))) if _fl else '',
        _pa(R.get('retenu')), fr(R.get('tx'), 1), _pa(R.get('gc')), _pa(S7.get('passe')), _pa(S7.get('consensus')),
        S7.get('lab', 'n.d.'), _l7.get('lab', 'n.d.'), _du(_l7.get('tm')), _du(_l7.get('H')), str(_l7.get('preuve', 'n.d.')).lower()))
    # V24 : decider -- que faire, fait cle, pari, voie B, juste sous le verdict
    _A, _F, _As, _C, _B = (R.get(k) or {} for k in ('action', 'fait_cle', 'asymetrie', 'confiance', 'voie_b'))
    v24 = []
    _Rc = R.get('recit') or {}
    if _Rc:  # V25 : la page 1 en une ligne
        v24.append('📖 Page 1 : %s — « %s » → %s' % (_Rc['etiquette'], _Rc['titre'], _Rc['action']))
    if _A:
        v24.append('🧭 Que faire (%s) : %s — %s%s' % ('ligne détenue' if _A.get('detenue') else 'nouvelle position', _A['act'], _A.get('pourquoi', ''),
                                                     ''.join(' · ' + _A[k] for k in ('ordre', 'voie_b', 'plan_tactique') if _A.get(k))))
    if _F:
        v24.append('🔑 Fait clé : %s' % _F['fait'])
    if _As or _C:
        v24.append('⚖️ Pari : si je me suis trompé %s · si j’ai raison %s · espérance pondérée %s · confiance %s%s' % (
            ('%s %%' % fr(_As.get('perte'), 0, True)) if num(_As.get('perte')) else 'n.d.',
            ('×%s' % fr(_As.get('fois'), 1)) if num(_As.get('fois')) else 'n.d.', _pa(_As.get('esp')),
            ('%s %%' % fr(_C.get('pct'), 0)) if _C else 'n.d.', (' → ' + _As['lab']) if _As.get('lab') else ''))
    if _B and _B.get('statut') not in ('', 'NON ÉVALUÉE', 'EN SUIVI'):
        v24.append('🎯 %s — %s%s' % (_B['lab'], _B['txt'], (' · objectif %s, stop temps %s' % (fprix(_B.get('vp')), _B.get('sortie_temps') or 'n.d.'))
                                    if _B.get('statut') in ('OUVERTE', 'EN ATTENTE') else ''))
    for i_, l_ in enumerate(v24):
        L.insert(2 + i_, l_)
    if S7:
        L.append('📈 Escalier : %s (FCF/BPA %s %% sur %s/%s exercices)' % (S7.get('clab'), fr(S7.get('conv'), 0), S7.get('ncv'), S7.get('nN')))
    M7 = R.get('monde') or {}
    if M7:
        L.append('🌍 Apport au monde : %s (+%s / −%s)' % (M7.get('lab', 'n.d.'), M7.get('P', 0), M7.get('N', 0)))
    if WARN:
        L.append('\u26a0\ufe0f ' + ' \u00b7 '.join(WARN))
    L.append(R['nico'])
    return '\n'.join(L)


# ------------------------------------------------------------------ V23.7 / V23.7.1 : les trois questions (lecture seule, R3)
# Combien je gagne ? De combien les benefices grandissent ? Combien de temps ca tient ? + V23.7.1 : apport au monde.
# Aucun effet sur Q, le taux exige, les prix, la taille, les tranches, les portes ni le verdict.
R_ACHETEUR, M_MATURE, N_MAX_DUREE = 9.0, 15.0, 40
DUREE_FARFELUE = 25  # V23.7.2 : au-dela de 25 ans de croissance supposes par le cours, la longevite n'est plus credible


def _nb(x):
    """Nombre fini depuis une valeur nue, une valeur [v, prov, src, note] ou un texte « 11,5 » ; sinon None."""
    if isinstance(x, list):
        x = x[0] if x else None
    if isinstance(x, bool) or x is None:
        return None
    if num(x):
        return float(x)
    if isinstance(x, str):
        try:
            v = _en_nombre(x)
        except (ValueError, TypeError):
            return None
        return float(v) if num(v) else None
    return None


def _doc(x):
    """Valeur documentee : nombre, provenance P/C/E et source datee."""
    m = V(x)
    return (_nb(x) is not None and m['prov'] in ('P', 'C', 'E')
            and isinstance(m['src'], str) and bool(re.search(DATE_PREUVE, m['src'])))


def _annee(lbl):
    m = re.search(r'(?<!\d)((?:19|20)\d{2})(?!\d)', str(lbl or ''))
    return int(m.group(1)) if m else None


def _cagr(a, b, n):
    if not (num(a) and num(b) and a > 0 and b > 0 and num(n) and n > 0):
        return None
    return 100 * ((b / a) ** (1.0 / n) - 1)


def _lignes_valides(tb):
    out = []
    for e in (tb.get('lignes') if isinstance(tb.get('lignes'), list) else []):
        if isinstance(e, (list, tuple)) and len(e) >= 2 and isinstance(e[1], list):
            out.append((str(e[0]), e[1]))
    return out


def _ligne(lignes, *mots):
    for nom, serie in lignes:
        n = _sans_accent(nom).upper()
        if any(m in n for m in mots):
            return serie
    return []


def _sur(fn, *args, defaut=''):
    """V23.7.1 : un module de lecture ne bloque jamais la livraison du dossier."""
    try:
        return fn(*args)
    except Exception as e:  # noqa: BLE001 - lecture seule, on signale et on continue
        warn('Module de lecture %s non affiché : entrée malformée (%s: %s).' % (fn.__name__, type(e).__name__, e))
        return defaut


# ---------------------------------------------------------------- (C, D) escalier et sources de croissance
def calc_sources(D, R):
    s = G(D, 'croissance.sources')
    s = s if isinstance(s, dict) else {}
    tb = G(D, 'croissance.tableau')
    tb = tb if isinstance(tb, dict) else {}
    annees = [str(a) for a in tb.get('annees')] if isinstance(tb.get('annees'), list) else []
    na = len(annees)
    lignes = _lignes_valides(tb)
    # n_estime : entier entre 0 et le nombre d'exercices, sinon deduit des libelles « e »
    ne_raw = tb.get('n_estime')
    nev = _nb(ne_raw)
    if ne_raw in (None, '') and na == 0:
        ne = 0
    elif nev is not None and float(nev).is_integer() and 0 <= nev <= na:
        ne = int(nev)
    else:
        ne = sum(1 for a in annees if re.search(r'\d{4}\s*[eE]\b|\d{4}[eE]$', a))
        if na:
            warn('croissance.tableau.n_estime invalide (%r) : %s année(s) projetée(s) déduite(s) des libellés.' % (ne_raw, ne))
    nh = na - ne

    def serie(*mots):
        x = [_nb(v) for v in _ligne(lignes, *mots)][:na]
        return x + [None] * (na - len(x))
    bpa, fcf = serie('BPA', 'EPS'), serie('FCF')
    bpa_h, fcf_h = bpa[:nh], fcf[:nh]
    # projection = scenario central, qui calcule le prix (source unique)
    C = G(D, 'valo.scenarios.central')
    cb = [_nb(x) for x in (C.get('bpa') if isinstance(C, dict) and isinstance(C.get('bpa'), list) else [])][:4]
    cb = cb + [None] * (4 - len(cb))
    y0 = _annee(G(D, 'valo.premier_exercice'))
    if ne == 4:
        lab_p = annees[nh:]
        fcf_p = fcf[nh:]
        diff = [i for i in range(4) if num(bpa[nh + i]) and num(cb[i]) and cb[i] != 0
                and abs(bpa[nh + i] - cb[i]) > 0.01 * abs(cb[i])]
        if diff:
            warn('BPA projetés du tableau différents du scénario central (%s) : tableau et escalier affichent le scénario central, qui calcule le prix.'
                 % ', '.join(lab_p[i] for i in diff))
    else:
        lab_p = ['%se' % (y0 + i) for i in range(4)] if y0 else ['an %d' % (i + 1) for i in range(4)]
        fcf_p = [None] * 4
        diff = []
        if ne:
            warn('Le tableau compte %s année(s) projetée(s) au lieu de 4 : l’escalier suit le scénario central, années déduites du premier exercice.' % ne)
    # tableau affiche : normalise, projections BPA = scenario central
    if na:
        lg = []
        for nom, ser in lignes:
            vals = [_nb(v) for v in ser][:na]
            vals = vals + [None] * (na - len(vals))
            if ne == 4 and _sans_accent(nom).upper().startswith(('BPA', 'EPS')) and any(num(c) for c in cb):
                vals = vals[:nh] + [c if num(c) else vals[nh + i] for i, c in enumerate(cb)]
            lg.append([nom, vals])
        R['tableau_aff'] = {'annees': annees, 'lignes': lg, 'n_estime': ne}
    # passe : toujours recalcule sur la serie qu'il cite
    idx = [i for i, v in enumerate(bpa_h) if num(v) and v > 0]
    pv = plab = None
    if len(idx) >= 2:
        i0, i1 = idx[0], idx[-1]
        ya, yb_ = _annee(annees[i0]), _annee(annees[i1])
        n = (yb_ - ya) if (ya and yb_ and yb_ > ya) else (i1 - i0)
        pv = _cagr(bpa_h[i0], bpa_h[i1], n)
        plab = 'BPA %s → %s du tableau' % (annees[i0], annees[i1])
    pd = _nb(s.get('passe'))
    pdm = V(s.get('passe'))
    note_passe = ''
    if pv is None and pd is not None:
        pv, plab = pd, ' · '.join(x for x in ('déclaré', pdm['src'], pdm['note']) if x)
    elif pv is not None and pd is not None and abs(pd - pv) > 2:
        note_passe = 'Passé déclaré %s %%/an (%s) : autre période que le tableau, non utilisé.' % (fr(pd, 1), pdm['note'] or pdm['src'] or 'période non précisée')
        warn('Croissance passée déclarée (%s %%/an) ≠ série du tableau (%s %%/an) : le dossier affiche la série.' % (fr(pd, 1), fr(pv, 1)))
    # base commune : dernier BPA publie positif
    base_i = idx[-1] if idx else None
    bb = bpa_h[base_i] if base_i is not None else None
    yb = _annee(annees[base_i]) if base_i is not None else None
    par_annee = {}
    for i, v in enumerate(bpa_h):
        if _annee(annees[i]) and num(v):
            par_annee[_annee(annees[i])] = v
    for i, v in enumerate(cb):
        if _annee(lab_p[i]) and num(v):
            par_annee[_annee(lab_p[i])] = v
    # consensus
    cv, cm = _nb(s.get('consensus')), V(s.get('consensus'))
    cons_i, hors = {}, []
    ylab = {_annee(l): i for i, l in enumerate(lab_p) if _annee(l)}
    for x in (s.get('consensus_bpa') if isinstance(s.get('consensus_bpa'), list) else []):
        if not (isinstance(x, list) and len(x) >= 2):
            continue
        v_, ya = _nb(x[1]), _annee(x[0])
        if v_ is None:
            continue
        if ya in ylab:
            cons_i[ylab[ya]] = v_
        else:
            hors.append(str(x[0]))
    if hors:
        warn('BPA du consensus sans exercice correspondant dans le scénario : %s (non affichés).' % ', '.join(hors))
    comp = None
    if cons_i and num(bb) and yb:
        k = max(cons_i)
        ym = _annee(lab_p[k])
        n = (ym - yb) if ym else None
        if n and n >= 1 and num(cb[k]):
            gn, gco = _cagr(bb, cb[k], n), _cagr(bb, cons_i[k], n)
            if num(gn) and num(gco):
                comp = (gn, gco, '%s → %s, même base publiée (BPA %s)' % (yb, lab_p[k], fr(bb, 2)))
    if comp is None and num(cv):
        per = re.findall(r'(?<!\d)((?:19|20)\d{2})(?!\d)', str(s.get('consensus_periode') or ''))
        if len(per) >= 2:
            y1, y2 = int(per[0]), int(per[-1])
            v0, v2 = par_annee.get(y1 - 1), par_annee.get(y2)
            gn = _cagr(v0, v2, y2 - (y1 - 1)) if (v0 and v2) else None
            if num(gn):
                comp = (gn, cv, '%s → %s, période du consensus' % (y1 - 1, y2))
    cons_aff = cv if num(cv) else (comp[1] if comp else None)
    defin = str(s.get('consensus_definition') or '').strip()
    motif = str(s.get('motif_ecart') or '').strip()
    if cons_aff is None:
        lab, lvl, txt = 'CONSENSUS NON DOCUMENTÉ', 'gris', 'Impossible de dire si notre central est plus prudent ou plus optimiste que les analystes.'
    elif comp is None:
        lab, lvl, txt = 'COMPARAISON NON HOMOGÈNE', 'gris', (
            'Les exercices du consensus ne sont pas rapprochés de notre scénario : renseigner consensus_bpa par exercice '
            'ou consensus_periode. Aucun classement plus prudent ou plus optimiste.')
    else:
        gn, gco, per_txt = comp
        d_ = gn - gco
        if d_ < -2:
            lab, lvl = 'PLUS PRUDENT QUE LE CONSENSUS', 5
        elif d_ <= 2:
            lab, lvl = 'ALIGNÉ SUR LE CONSENSUS', 5
        elif motif:
            lab, lvl = 'PLUS OPTIMISTE QUE LE CONSENSUS — MOTIF ÉCRIT', 4
        else:
            lab, lvl = 'PLUS OPTIMISTE QUE LE CONSENSUS — SANS MOTIF', 3
            warn('Notre central dépasse le consensus de %s pts sur %s sans motif écrit (croissance.sources.motif_ecart).' % (fr(d_, 1), per_txt))
        txt = 'Sur %s : nous %s %%/an, les analystes %s %%/an.' % (per_txt, fr(gn, 1), fr(gco, 1))
        if motif and d_ > 2:
            txt += ' Motif : %s' % motif
    txt += (' BPA du consensus : %s.' % defin) if defin else ' Définition du BPA du consensus non précisée (publié ou ajusté).'
    gc = R.get('gc')
    if num(gc) and num(pv) and gc > pv + 3:
        txt += ' Notre central accélère de %s pts par rapport au passé : le pont du §5 doit l’expliquer.' % fr(gc - pv, 1)
    # guidance dans sa metrique native
    gv, gmeta = _nb(s.get('guidance')), V(s.get('guidance'))
    gmet = str(s.get('guidance_metrique') or '').strip().upper()
    gdeduit = False
    if not gmet:
        t_ = _sans_accent(' '.join((gmeta['note'], gmeta['src']))).upper()
        for cle, nom in (('BPA', 'BPA'), ('EPS', 'BPA'), ('EBIT', 'EBIT'), ('CHIFFRE D', 'CA'), (' CA ', 'CA'), ('REVENU', 'CA')):
            if cle in ' %s ' % t_:
                gmet, gdeduit = nom, True
                break
    gper = str(s.get('guidance_periode') or '').strip()
    # conversion du BPA en cash : couverture affichee
    paires = [(b_, f_) for b_, f_ in zip(bpa_h, fcf_h) if num(b_) and num(f_)]
    sb = sum(b_ for b_, _ in paires)
    conv = 100 * sum(f_ for _, f_ in paires) / sb if (paires and sb > 0) else None
    ncv, nN = len(paires), nh
    if est_financier(D):
        clab, clvl = 'N.A. — SECTEUR FINANCIER', 'gris'
    elif not num(conv):
        clab, clvl = 'CONVERSION NON MESURÉE', 'gris'
    elif ncv < 3 or ncv < 0.6 * nN:
        clab, clvl = 'CONVERSION PARTIELLE (%s/%s EXERCICES)' % (ncv, nN), 'gris'
    elif conv >= 90:
        clab, clvl = 'LE CASH SUIT LES BÉNÉFICES', 5
    elif conv >= 70:
        clab, clvl = 'CONVERSION CORRECTE', 4
    else:
        clab, clvl = 'BÉNÉFICES PEU CONVERTIS EN CASH', 3
    R['sources_g'] = dict(
        lab=lab, lvl=lvl, txt=txt, passe=pv, plab=plab, note_passe=note_passe, consensus=cons_aff, cmeta=cm,
        cper=str(s.get('consensus_periode') or '').strip(), comp=comp, guid=gv, gmeta=gmeta, gmet=gmet, gdeduit=gdeduit, gper=gper,
        conv=conv, ncv=ncv, nN=nN, clab=clab, clvl=clvl, diverge=bool(diff),
        annees=annees[:nh] + list(lab_p), nh=nh, bpa=bpa_h + cb, fcf=fcf_h + list(fcf_p), cons_i={nh + i: v for i, v in cons_i.items()})


def _lvl_g(g):
    return 'gris' if not num(g) else 5 if g >= 10 else 4 if g >= 5 else 3 if g > 0 else 2


COUL_BPA, COUL_FCF = '#b79cff', '#26d0e3'  # V24.1 : code couleur de Nico (indicateur NICO E2) : benefice mauve, free cash flow turquoise


def escalier_svg(S):
    """Barres BPA (cyan) et FCF par action (vert) ; passe plein, projection du scenario central hachuree ; consensus en losanges."""
    an, bpa, fcf, nh, cons_i = S['annees'], S['bpa'], S['fcf'], S['nh'], S['cons_i']
    n = len(an)
    vals = [x for x in list(bpa) + list(fcf) + list(cons_i.values()) if num(x)]
    if n < 2 or not vals or max(vals) <= 0:
        return ''
    W, H, gl, gr, gt_, gb = 960, 340, 52, 16, 40, 44
    mx = max(vals) * 1.12
    mn = min(0.0, min(vals))
    pw = (W - gl - gr) / n
    bw = min(30, pw * 0.32)
    y = lambda v: gt_ + (H - gt_ - gb) * (1 - (v - mn) / (mx - mn))
    o = ['<svg viewBox="0 0 %d %d" role="img" aria-label="BPA et FCF par action" style="width:100%%;height:auto;display:block">' % (W, H),
         '<defs><pattern id="hc" width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">'
         '<rect width="6" height="6" fill="#0c1113"/><rect width="3" height="6" fill="#b79cff"/></pattern>'
         '<pattern id="hv" width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">'
         '<rect width="6" height="6" fill="#0c1113"/><rect width="3" height="6" fill="#26d0e3"/></pattern></defs>']
    for k in range(5):
        v = mn + (mx - mn) * k / 4
        o.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#1d2a2e"/>' % (gl, W - gr, y(v), y(v)))
        o.append('<text x="%d" y="%.1f" fill="#7e979d" font-size="13" text-anchor="end" font-family="monospace">%s</text>' % (
            gl - 6, y(v) + 4, esc(fr(v, 2))))
    if 0 < nh < n:
        xs = gl + pw * nh
        o.append('<line x1="%.1f" x2="%.1f" y1="%d" y2="%d" stroke="#39d6e0" stroke-dasharray="4 4" opacity=".6"/>' % (xs, xs, gt_ - 8, H - gb))
        o.append('<text x="%.1f" y="%d" fill="#a9c0c5" font-size="14" text-anchor="end" font-family="monospace">publié</text>' % (xs - 8, gt_ - 14))
        o.append('<text x="%.1f" y="%d" fill="#39d6e0" font-size="14" font-family="monospace">scénario central</text>' % (xs + 8, gt_ - 14))
    y0 = y(0)
    for i, a in enumerate(an):
        cx = gl + pw * (i + 0.5)
        proj = i >= nh
        for j, (serie, plein, hach) in enumerate(((bpa, COUL_BPA, 'url(#hc)'), (fcf, COUL_FCF, 'url(#hv)'))):
            v = serie[i] if i < len(serie) else None
            if not num(v):
                continue
            x = cx - bw - 1 if j == 0 else cx + 1
            top, bot = min(y(v), y0), max(y(v), y0)
            o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" rx="2" fill="%s" stroke="%s" stroke-width="%s"/>' % (
                x, top, bw, max(1.0, bot - top), hach if proj else plein, plein, '1' if proj else '0'))
            if j == 0:
                ylab = min(top, y(cons_i[i]) - 9) if i in cons_i else top
                o.append('<text x="%.1f" y="%.1f" fill="#e8f2f4" font-size="13" text-anchor="middle" font-family="monospace">%s</text>' % (
                    x + bw / 2, ylab - 6, esc(fr(v, 2))))
        o.append('<text x="%.1f" y="%d" fill="%s" font-size="14" text-anchor="middle" font-family="monospace">%s</text>' % (
            cx, H - gb + 20, '#39d6e0' if proj else '#a9c0c5', esc(a)))
    for i, v in cons_i.items():
        cx = gl + pw * (i + 0.5) - bw / 2 - 1
        o.append('<path d="M%.1f %.1f l7 7 l-7 7 l-7 -7 z" fill="#f2cf5b" stroke="#000" stroke-width="1"/>' % (cx, y(v) - 7))
    ly = H - 6
    o.append('<rect x="%d" y="%d" width="12" height="10" fill="#b79cff"/><text x="%d" y="%d" fill="#a9c0c5" font-size="13" font-family="monospace">Bénéfice par action</text>' % (gl, ly - 9, gl + 17, ly))
    o.append('<rect x="%d" y="%d" width="12" height="10" fill="#26d0e3"/><text x="%d" y="%d" fill="#a9c0c5" font-size="13" font-family="monospace">Free cash flow par action</text>' % (gl + 190, ly - 9, gl + 207, ly))
    if cons_i:
        o.append('<path d="M%d %d l6 6 l-6 6 l-6 -6 z" fill="#f2cf5b"/><text x="%d" y="%d" fill="#a9c0c5" font-size="13" font-family="monospace">BPA attendu par les analystes</text>' % (gl + 420, ly - 11, gl + 432, ly))
    o.append('</svg>')
    return ''.join(o)


def croissance_html(D, R, dev):
    """Episode 2 : de combien les benefices grandissent, et le cash suit-il ?"""
    S = R.get('sources_g') or {}
    if not S:
        return ''
    an, bpa, nh = S['annees'], S['bpa'], S['nh']
    phrase = ''
    hist = [(an[i], bpa[i]) for i in range(nh) if num(bpa[i]) and bpa[i] > 0]
    if len(hist) >= 2 and num(S.get('passe')) and S.get('plab', '').startswith('BPA'):
        phrase = 'Le BPA est passé de %s à %s entre %s et %s (%s %%/an)' % (
            fr(hist[0][1], 2), fr(hist[-1][1], 2), esc(hist[0][0]), esc(hist[-1][0]), fr(S['passe'], 1, True))
        if num(bpa[-1]):
            phrase += ' ; le scénario central l’emmène à %s en %s, soit %s %%/an depuis la base normalisée.' % (
                fr(bpa[-1], 2), esc(an[-1]), fr(R.get('gc'), 1, True))
        else:
            phrase += '.'
    svg = escalier_svg(S)
    if num(S.get('conv')):
        conv_txt = ('Sur les %s exercices publiés où BPA et FCF par action sont connus (sur %s), %s %% du BPA est devenu du cash disponible.'
                    % (S['ncv'], S['nN'], fr(S['conv'], 0)))
    else:
        conv_txt = 'Conversion en cash non mesurée : séries BPA ou FCF par action incomplètes.'
    if S['clab'].startswith('N.A.'):
        conv_txt = 'Pour une banque ou un assureur, le FCF n’a pas le même sens : conversion non appliquée.'
    note_div = (' <b>Le tableau saisi différait du scénario central : c’est le scénario central qui est affiché.</b>'
                if S.get('diverge') else '')
    bloc_esc = ('<div class="c"><h3>📈 L’escalier des bénéfices</h3><p>%s</p>%s<div style="margin-top:12px">%s</div>'
                '<div class="sub">%s En mauve le bénéfice par action, en turquoise le free cash flow par action ; les barres hachurées sont les projections du scénario central%s.%s</div></div>') % (
        phrase or 'Séries BPA et FCF par action à compléter dans croissance.tableau.', svg,
        bdg(S['clab'], S['clvl'], 'gros wrap'), conv_txt,
        ' ; losanges jaunes = BPA attendu par les analystes' if S.get('cons_i') else '', note_div) if (svg or phrase) else ''
    mxv = max([abs(v) for v in (S.get('passe'), S.get('consensus'), S.get('guid'), R.get('gc')) if num(v)] + [1.0])

    def ligne(titre, v, metrique, detail, accent=False, compare=True):
        larg = max(0.0, min(100.0, 100 * v / mxv)) if num(v) else 0
        return ('<div style="margin:12px 0"><div style="display:flex;justify-content:space-between;gap:12px">'
                '<span>%s <span class="lab">· %s</span></span><b class="t%s" style="font-family:ui-monospace,monospace">%s</b></div>'
                '<div class="bar"><i style="width:%s%%;background:%s"></i></div><div class="lab" style="margin-top:4px">%s</div></div>') % (
            ('<b style="color:%s">%s</b>' % (COUL_BPA, esc(titre))) if accent else esc(titre), esc(metrique),
            (_lvl_g(v) if compare else 'gris') if num(v) else 'gris', ('%s %%/an' % fr(v, 1)) if num(v) else 'n.d.',
            fr(larg, 0), COUL_BPA if accent else ('var(--txt2)' if compare else 'var(--gris)'), detail)
    cm, gm = S['cmeta'], S['gmeta']
    gmet = S['gmet'] or 'métrique non précisée'
    rows = [ligne('Le passé', S.get('passe'), 'BPA', esc(S.get('plab') or 'non documenté')),
            ligne('Les analystes', S.get('consensus'), 'BPA', esc(' · '.join(x for x in (
                cm['src'], S['cper'], cm['note'], '' if num(_nb(cm['v'])) or not S.get('comp') else 'calculé sur les BPA attendus') if x)) or 'non documenté'),
            ligne('La direction (guidance)', S.get('guid'), gmet + (' (déduite de la note)' if S.get('gdeduit') else ''), esc(' · '.join(x for x in (
                gm['src'], S['gper'], gm['note']) if x)) + ('' if gmet == 'BPA' or not num(S.get('guid')) else
                                                         ' — <b>autre métrique : non comparée au BPA</b>'), compare=(gmet == 'BPA')),
            ligne('Notre scénario central', R.get('gc'), 'BPA', 'base normalisée → 4e exercice', accent=True)]
    return ('%s<div class="c"><h3>🧮 Qui prévoit quoi ?</h3>'
            '<p class="sub" style="margin-top:0">Chaque prévision dans sa métrique et sur sa période. Seules les prévisions de BPA se comparent entre elles.</p>'
            '<div class="grid g2" style="gap:6px 40px">%s</div><div style="margin-top:14px">%s</div><p class="sub">%s%s</p></div>') % (
        bloc_esc, ''.join(rows), bdg(S['lab'], S['lvl'], 'gros wrap'), esc(S['txt']),
        (' ' + esc(S['note_passe'])) if S.get('note_passe') else '')


# ---------------------------------------------------------------- (B) duree de croissance supposee
def annees_implicites(mult, g, p, r=R_ACHETEUR, m0=M_MATURE):
    """Annees de croissance a g %/an, apres l'an 4, qu'un multiple de sortie suppose.

    L'acheteur de l'an 4 exige r %/an. Pendant n annees, la societe croit de g %/an et distribue la part p de ses
    benefices ; ensuite elle vaut m0 fois ses benefices. On cherche n tel que la valeur atteigne le multiple.
    Chaque annee ajoute q^(n-1).(p.q + m0.(q-1)), q = (1+g)/(1+r) : signe constant, donc monotone.
    """
    if not (num(mult) and num(g) and num(p)):
        return None, 'n.d.'
    if mult <= m0 + 1e-9:
        return 0.0, 'aucune'
    q = (1 + g / 100.0) / (1 + r / 100.0)
    if p * q + m0 * (q - 1) <= 1e-12:
        return None, 'inatteignable'
    prev, cumul = m0, 0.0
    for n in range(1, N_MAX_DUREE + 1):
        cumul += p * q ** n
        cur = cumul + m0 * q ** n
        if cur >= mult - 1e-9:
            return (n - 1) + (mult - prev) / (cur - prev), 'ok'
        prev = cur
    return None, 'au-delà'


def _diag_duree(tot, etat, H, qui):
    """Diagnostic d'une duree supposee (qui = 'NOTRE MULTIPLE' ou 'LE COURS') face a la duree estimee H."""
    if etat in ('inatteignable', 'au-delà'):
        return ('%s N’EST PAS JUSTIFIÉ PAR LA CROISSANCE' % qui, 2 if qui == 'LE COURS' else 3)
    if etat == 'aucune':
        return ('%s NE SUPPOSE AUCUNE CROISSANCE APRÈS L’AN 4' % qui, 5)
    if not num(tot):
        return ('NON CALCULABLE', 'gris')
    if not num(H):
        return ('DURÉE À DOCUMENTER', 'gris')
    if tot <= H + 1e-9:
        return ('%s EST COUVERT PAR LA DURÉE ESTIMÉE' % qui, 5)
    if tot <= H + 3:
        return ('%s DÉPASSE UN PEU LA DURÉE ESTIMÉE' % qui, 4)
    return ('%s SUPPOSE PLUS QUE LA DURÉE ESTIMÉE' % qui, 3)


def calc_duree(D, R):
    """V23.7.1 : annees de croissance supposees par notre multiple de sortie et par le cours, face a la duree estimee."""
    scs = G(D, 'valo.scenarios') or {}
    C = scs.get('central') if isinstance(scs, dict) else None
    b = R.get('boule_neige') or {}
    H = b.get('horizon') if num(b.get('horizon')) else None
    hm = V(G(D, 'boule_neige.horizon_ans'))
    out = {'horizon': H, 'h_prov': hm['prov'] or 'E', 'r': R_ACHETEUR, 'm0': M_MATURE, 'notes': []}
    R['duree'] = out
    if not (R.get('calc') and isinstance(C, dict) and isinstance(C.get('bpa'), list) and len(C['bpa']) >= 4):
        out.update(lab='DURÉE NON CALCULÉE', lvl='gris', lab_m='NON CALCULABLE', lvl_m='gris',
                   txt='Scénarios non chiffrés : aucune durée supposée calculable.')
        return
    bpa = [_nb(x) for x in C['bpa'][:4]]
    # perimetre du multiple : BPA d'exploitation quand la tresorerie est comptee a part (V22.7.1)
    pf = _nb(C.get('produit_fin_an4'))
    if pf is None:
        pf = _nb(G(D, 'valo.produit_financier_action')) or 0.0
    e3 = bpa[2] - pf if num(bpa[2]) else None
    e4 = bpa[3] - pf if num(bpa[3]) else None
    g_ps = 100 * (e4 / e3 - 1) if (num(e3) and e3 > 0 and num(e4) and e4 > 0) else None
    if pf:
        out['notes'].append('croissance mesurée sur le BPA d’exploitation (hors produit financier de %s), périmètre du multiple' % fr(pf, 2))
    tr = entrees_autofinancement(D)
    va = _nb(tr.get('variation_actions'))
    if num(g_ps) and num(va):
        g = 100 * ((1 + g_ps / 100) * (1 + va / 100) - 1)
        out['notes'].append('croissance du bénéfice total = BPA %s %% et actions %s %%/an : les rachats sont comptés dans la distribution, pas deux fois'
                            % (fr(g_ps, 1, True), fr(va, 1, True)))
    else:
        g = g_ps
        if num(g_ps):
            out['notes'].append('évolution du nombre d’actions non renseignée : rachats non séparés de la croissance')
    # rendement des nouveaux investissements : meme nature que la croissance
    rb = R.get('rentab') or {}
    met = str(rb.get('metrique') or 'ROIC').upper()
    if est_financier(D) and _nb(tr.get('roe')) is not None:
        ronic, src, approx = _nb(tr.get('roe')), 'ROE attendu' + ('' if _doc(tr.get('roe')) else ' (source non datée)'), not _doc(tr.get('roe'))
    elif _nb(tr.get('rendement_marginal')) is not None and _nb(tr.get('rendement_marginal')) > 0:
        ok = _doc(tr.get('rendement_marginal'))
        ronic, src, approx = _nb(tr.get('rendement_marginal')), (
            'rendement des nouveaux investissements documenté' if ok else 'rendement des nouveaux investissements NON SOURCÉ (approximation)'), not ok
    elif met in ('ROIC', 'ROCE APRÈS IMPÔT', 'ROCE APRES IMPOT') and num(rb.get('med')) and rb['med'] > 0:
        ronic, src, approx = rb['med'], '%s médian du dossier (approximation)' % met, True
    else:
        ronic, src, approx = None, '', True
    besoin = False
    if num(ronic) and ronic > 0 and num(g):
        if g > ronic:
            besoin = True
            out['notes'].append('la croissance (%s %%) dépasse le rendement des nouveaux investissements (%s %%) : elle suppose un financement externe, durée conditionnelle'
                                % (fr(g, 1), fr(ronic, 1)))
        p = max(0.0, min(1.0, 1 - max(g, 0) / ronic))
        p_txt = '1 − %s / %s = %s %% des bénéfices distribuables (%s)' % (fr(g, 1), fr(ronic, 1), fr(100 * p, 0), src)
    else:
        dps = _nb((C.get('dps') or [None] * 4)[3] if isinstance(C.get('dps'), list) and len(C['dps']) >= 4 else None)
        p = max(0.0, min(1.0, dps / bpa[3])) if (num(dps) and num(bpa[3]) and bpa[3] > 0) else 0.0
        p_txt = 'dividende seul : %s %% des bénéfices (prudent, rendement des nouveaux investissements non documenté)' % fr(100 * p, 0)
    ct = _nb(G(D, 'valo.croissance_terminale'))
    if ct is not None and num(g):
        out['notes'].append('hypothèse de lecture : la croissance de l’an 4 (%s %%) se prolonge ; la croissance terminale retenue dans les flux est %s %%'
                            % (fr(g, 1), fr(ct, 1)))
    mc, me = _nb(C.get('multiple')), R.get('mult_exige')
    n_c, e_c = annees_implicites(mc, g, p)
    n_m, e_m = annees_implicites(me, g, p) if num(me) else (None, 'n.d.')
    sens = {r_: annees_implicites(mc, g, p, r_)[0] for r_ in (8.0, 9.0, 10.0)}
    tot_c = (4 + n_c) if num(n_c) else None
    tot_m = (4 + n_m) if num(n_m) else None
    out.update(g=g, p=p, p_txt=p_txt, mc=mc, me=me, n_c=n_c, e_c=e_c, n_m=n_m, e_m=e_m, tot_c=tot_c, tot_m=tot_m,
               sens={k: (4 + v) if num(v) else None for k, v in sens.items()}, approx=approx or besoin, besoin=besoin)
    if not num(g) or g <= 0:
        lab, lvl = 'CROISSANCE ÉTEINTE EN AN 4', 4 if (num(mc) and mc <= M_MATURE) else 3
        lab_m, lvl_m = lab, lvl
        txt = 'Le central ne croît plus en fin d’horizon : seul un multiple de sortie ≤ %s× se passe de croissance future.' % fr(M_MATURE, 0)
    else:
        lab, lvl = _diag_duree(tot_c, e_c, H, 'NOTRE MULTIPLE')
        lab_m, lvl_m = _diag_duree(tot_m, e_m, H, 'LE COURS')
        def dur(t, e):
            return 'aucune année au-delà de l’an 4' if e == 'aucune' else ('~%s ans' % fr(t, 0)) if num(t) else (
                'plus que ce que la croissance peut justifier' if e in ('inatteignable', 'au-delà') else 'n.d.')
        txt = 'Durée estimée : %s. Notre multiple de sortie (%s×) en suppose %s ; au cours du jour, atteindre ton seuil en suppose %s.' % (
            ('~%s ans' % fr(H, 0)) if num(H) else 'à documenter', fr(mc, 1), dur(tot_c, e_c), dur(tot_m, e_m))
        if out['approx']:
            txt += ' Lecture approximative : voir les limites dans le détail.'
    out.update(lab=lab, lvl=lvl, lab_m=lab_m, lvl_m=lvl_m, txt=txt)


def duree_html(R):
    """V24 : une seule question -- combien d'annees de croissance le prix exige-t-il, et combien en voit-on ?"""
    d = R.get('duree') or {}
    if not d:
        return ''
    L = R.get('longevite') or {}
    H, tc, tm = d.get('horizon'), d.get('tot_c'), d.get('tot_m')
    mx = max([x for x in (H, tc, tm, 10) if num(x)]) * 1.1
    al = R.get('alignement') or {}
    try:
        an0 = int(str(al.get('sortie'))[-4:]) - 4
    except (TypeError, ValueError):
        an0 = None
    def jusqu(t):
        return (' (jusqu’en %s)' % (an0 + int(round(t)))) if (an0 and num(t)) else ''

    def barre(lab, v, coul, txt, vide):
        w = max(0.0, min(100.0, 100 * v / mx)) if num(v) else 0
        return ('<div style="margin:14px 0"><div style="display:flex;justify-content:space-between;gap:12px"><span>%s</span>'
                '<b style="font-family:ui-monospace,monospace;color:%s">%s</b></div><div class="bar" style="height:16px">'
                '<i style="width:%s%%;background:%s"></i></div><div class="lab" style="margin-top:4px">%s</div></div>') % (
            esc(lab), coul, ('~%s ans' % fr(v, 0)) if num(v) else esc(vide), fr(w, 0), coul, esc(txt))

    def vide(e):
        return 'aucune après l’an 4' if e == 'aucune' else 'non justifiable' if e in ('inatteignable', 'au-delà') else 'n.d.'
    g = d.get('g')
    if num(tm) and num(H):
        tete = ('Pour gagner ton seuil de %s %%/an au cours du jour, il faut que les bénéfices grandissent encore <b>~%s ans</b>%s, puis plus rien. '
                'On voit de quoi tenir <b>~%s ans</b>%s. %s') % (
            fr(R.get('tx'), 0), fr(tm, 0), jusqu(tm), fr(H, 0), jusqu(H),
            ('Écart : %s an%s à croire sans preuve.' % (fr(L['gap'], 0), 's' if L['gap'] >= 1.5 else '')) if num(L.get('gap')) and L['gap'] > 0
            else 'Le prix ne te demande pas de croire plus loin que ce qu’on voit.')
    elif num(tm):
        tete = 'Pour gagner ton seuil au cours du jour, il faut ~%s ans de croissance%s. La durée visible n’est pas documentée.' % (fr(tm, 0), jusqu(tm))
    else:
        tete = esc(d.get('txt') or 'Durée non calculable.')
    bars = (barre('Ce que le prix du jour exige', tm, 'var(--txt2)',
                  ('les 4 années modélisées + %s ans à %s %%/an pour que le marché paie %s× en sortie' % (fr(d.get('n_m'), 0), fr(g, 1), fr(d.get('me'), 1)))
                  if num(tm) and num(d.get('n_m')) and d.get('n_m') > 0.05 else
                  'les 4 années modélisées suffisent : le multiple de sortie exigé (%s×) ne suppose plus aucune croissance' % fr(d.get('me'), 1)
                  if num(tm) else 'multiple exigé %s×' % fr(d.get('me'), 1), vide(d.get('e_m')))
            + barre('Ce qu’on voit (%s)' % ('estimation' if d.get('h_prov') == 'E' else 'provenance %s' % d.get('h_prov')),
                    H, 'var(--txt2)', 'débouchés, contrats et protection documentés dans la boule de neige', 'à documenter'))
    sens = d.get('sens') or {}
    notes = ''.join('<li>%s</li>' % esc(n_) for n_ in d.get('notes') or [])
    det = ('<details><summary>Notre multiple de sortie, les conventions et les limites</summary>%s<p class="sub">Le multiple de sortie paie les années '
           'de croissance après l’horizon de 4 ans. Conventions : l’acheteur de l’an 4 exige %s %%/an ; une fois la croissance terminée, '
           'la société vaut %s× ses bénéfices. Pendant la croissance, la part distribuable vaut %s. Sensibilité de notre multiple (durée totale, 4 ans '
           'modélisés compris) : %s.</p>%s<p class="sub">C’est une traduction du multiple sous ces conventions, pas une mesure du moat ni une '
           'prévision du marché. Lecture seulement : aucun effet sur le prix, le taux exigé ni le verdict.</p></details>') % (
        barre('Ce que suppose notre multiple de sortie (%s×)' % fr(d.get('mc'), 1), tc, 'var(--txt2)',
              '4 ans modélisés + %s ans à %s %%/an' % (fr(d.get('n_c'), 0), fr(g, 1)) if num(tc) else 'multiple %s×' % fr(d.get('mc'), 1), vide(d.get('e_c'))),
        fr(d['r'], 0), fr(d['m0'], 0), esc(d.get('p_txt') or 'n.d.'),
        ' · '.join('acheteur à %s %% → %s' % (fr(r_, 0), ('~%s ans' % fr(n_, 0)) if num(n_) else 'n.d.') for r_, n_ in sorted(sens.items())),
        ('<ul class="sub">%s</ul>' % notes) if notes else '')
    return ('<div class="c capital-box"><h3>⏳ Combien d’années de croissance le prix exige-t-il ?</h3>'
            '<div>%s %s</div><p style="margin-top:12px">%s</p>%s%s</div>') % (
        bdg(L.get('lab', 'n.d.'), L.get('lvl', 'gris'), 'gros wrap'),
        bdg('Preuves de durée : %s' % L.get('preuve', 'n.d.'), L.get('preuve_lvl', 'gris'), 'wrap'), tete, bars, det)


# ---------------------------------------------------------------- (A) pilote
def _phrase_prix(D, R):
    """La phrase de prix suit les portes reellement calculees, jamais le seul rendement."""
    meta = D.get('meta') or {}
    dev = esc(meta.get('devise', ''))
    cours = _nb(meta.get('cours'))
    vf = str(R.get('verdict_final') or '').upper()
    if not R.get('calc'):
        return 'Le dossier s’arrête avant la valorisation : pas de prix d’achat calculé.'
    rt, tx = R.get('retenu'), R.get('tx')
    base = 'Au cours de %s %s, rendement net estimé %s %%/an pour un seuil de %s %%' % (fprix(cours), dev, fr(rt, 1), fr(tx, 0))
    if not R.get('valorisation_valide'):
        return base + ', mais la valorisation n’est pas validée (ancrage du multiple ou clause) : aucun prix d’achat retenu.'
    if not num(R.get('PA')):
        return base + ', mais aucun prix ne respecte la règle des −40 % : achat impossible.'
    if R.get('porte_prix') == 'ouverte':
        ph = base + ' : le cours est dans ta zone d’achat (sous le prix maximum d’achat de %s %s).' % (fprix(R['PA']), dev)
        if not vf.startswith(('ACHAT', 'RENFORCEMENT')):
            ph += ' L’achat reste suspendu au verdict : %s.' % esc(R.get('verdict_final') or 'n.d.')
        return ph
    if num(rt) and num(tx) and rt >= tx and R.get('plancher_limite'):
        return base + ', mais la règle des −40 %% limite le prix maximum d’achat à %s %s : patience.' % (fprix(R['PA']), dev)
    return base + ' : patience jusqu’au prix maximum d’achat de %s %s.' % (fprix(R['PA']), dev)


QUALITE_PALIERS = ((85, 'ENTREPRISE EXCEPTIONNELLE', 6), (80, 'ENTREPRISE DE GRANDE QUALITÉ', 5), (75, 'ENTREPRISE DE QUALITÉ', 5),
                   (70, 'BONNE ENTREPRISE', 4), (65, 'ENTREPRISE DE QUALITÉ MOYENNE', 3), (60, 'ENTREPRISE DONT LA QUALITÉ EST À SURVEILLER', 3),
                   (-1e9, 'ENTREPRISE RISQUÉE', 2))


def lab_qualite(Q):
    """V23.7.2 : etiquette de la note de qualite, paliers fixes par Nico (07/11/2026)."""
    if not num(Q):
        return 'QUALITÉ NON ÉVALUÉE', 'gris'
    for seuil, lab, lvl in QUALITE_PALIERS:
        if Q >= seuil:
            return lab, lvl


def calc_longevite(R):
    """V24 : longevite = ce que le PRIX exige comme annees de croissance, face a ce qu'on VOIT (duree estimee).
    Le verdict principal porte sur l'ecart ; le niveau de preuve devient un badge secondaire. Lecture seule."""
    d, b = R.get('duree') or {}, R.get('boule_neige') or {}
    H, tm, em = d.get('horizon'), d.get('tot_m'), d.get('e_m')
    bl = str(b.get('lab') or '')
    etayee = bl == 'BOULE DE NEIGE ÉTAYÉE'
    preuve = ('ÉTAYÉE', 5) if etayee else ('À DOCUMENTER', 'gris') if bl in ('', 'BOULE DE NEIGE À DOCUMENTER') else ('PEU PROUVÉE', 3)
    gap = (tm - H) if (num(tm) and num(H)) else None
    if bl == 'CROISSANCE DESTRUCTRICE':
        lab, lvl, txt = 'PAS CRÉDIBLE', 2, 'grandir détruit de la valeur : les nouveaux investissements rapportent moins que leur coût'
    elif em in ('inatteignable', 'au-delà'):
        lab, lvl, txt = 'PAS CRÉDIBLE', 2, 'aucune durée de croissance réaliste ne justifie le cours du jour'
    elif num(tm) and tm >= DUREE_FARFELUE:
        lab, lvl, txt = 'PAS CRÉDIBLE', 2, 'le cours suppose ~%s ans de croissance d’affilée (au-delà de %s ans, c’est farfelu)' % (fr(tm, 0), DUREE_FARFELUE)
    elif not num(tm):
        lab, lvl, txt = 'À DOCUMENTER', 'gris', 'durée exigée par le cours non calculable'
    elif not num(H):
        lab, lvl, txt = 'À DOCUMENTER', 'gris', 'le prix exige ~%s ans de croissance ; la durée visible n’est pas documentée' % fr(tm, 0)
    elif gap <= 1e-9:
        lab, lvl, txt = 'LE PRIX NE PARIE PAS SUR LA DURÉE', 5, 'le prix exige ~%s ans de croissance, on en voit ~%s' % (fr(tm, 0), fr(H, 0))
    elif gap <= 2 + 1e-9:
        lab, lvl, txt = 'ÉCART FAIBLE', 4, 'le prix exige ~%s ans, on en voit ~%s : %s an%s de plus à croire' % (
            fr(tm, 0), fr(H, 0), fr(gap, 0), 's' if gap >= 1.5 else '')
    elif gap <= 5 + 1e-9:
        lab, lvl, txt = 'LE PRIX PARIE SUR LA DURÉE', 3, 'le prix exige ~%s ans, on en voit ~%s : %s ans à croire sans preuve' % (fr(tm, 0), fr(H, 0), fr(gap, 0))
    else:
        lab, lvl, txt = 'LE PRIX PARIE TROP LOIN', 2, 'le prix exige ~%s ans, on en voit ~%s : %s ans à croire sans preuve' % (fr(tm, 0), fr(H, 0), fr(gap, 0))
    R['longevite'] = dict(lab=lab, lvl=lvl, txt=txt, gap=gap, H=H, tm=tm, preuve=preuve[0], preuve_lvl=preuve[1],
                          feu=bool(num(gap) and gap <= 1e-9 and lab != 'PAS CRÉDIBLE'))


def pilote_html(D, R):
    """V23.7.2 : le generique (Qualite -> Rendement -> Croissance -> Longevite) puis le bandeau des feux."""
    meta = D.get('meta') or {}
    dev = esc(meta.get('devise', ''))
    S, d = R.get('sources_g') or {}, R.get('duree') or {}
    calc_longevite(R)
    L = R['longevite']
    q = R.get('q') or {}
    Q, gc, H = q.get('Q'), R.get('gc'), d.get('horizon')
    P = dict(portes(D, R))
    qlab, qlvl = lab_qualite(Q)
    # etapes du generique
    f_q = P.get('Qualité')
    f_r = P.get('Prix')
    f_c = P.get('Croissance')
    f_l = L['feu']
    rt = R.get('retenu')
    if not R.get('calc'):
        r_et, r_lvl = 'valorisation non exécutée', 'gris'
    elif f_r:
        r_et, r_lvl = 'dans ta zone d’achat', 5
    elif num(rt) and num(R.get('tx')) and rt >= R['tx']:
        r_et, r_lvl = 'seuil atteint, prix bloqué', 3
    else:
        r_et, r_lvl = 'patience jusqu’à %s %s' % (fprix(R.get('PA')), dev) if num(R.get('PA')) else 'aucun prix d’achat', R.get('niv_retenu', 'gris')
    lab_c = S.get('lab', '')
    c_et = ('plus prudent que les analystes' if lab_c.startswith('PLUS PRUDENT') else 'comme les analystes' if lab_c.startswith('ALIGNÉ')
            else 'plus optimiste que les analystes' if lab_c.startswith('PLUS OPTIMISTE') else 'BPA par action, scénario central')
    def etape(icone, titre, valeur, lvl, etiquette, sous=''):
        return ('<div class="gen-e"><div class="lab">%s %s</div><div class="gen-v t%s">%s</div>%s%s</div>') % (
            icone, esc(titre), lvl, valeur, bdg(etiquette, lvl, 'wrap'), ('<div class="lab" style="margin-top:6px">%s</div>' % sous) if sous else '')
    fl_, fp_ = _pilier_faible(R)
    e1 = etape('🏛️', 'Qualité', ('%s %%' % fr(Q, 0)) if num(Q) else 'n.d.', qlvl,
               qlab + (' (PROVISOIRE)' if q.get('provisoire') else ''),
               ('point faible : %s (%s %%)' % (esc(fl_.lower()), fr(fp_, 0))) if fl_ else '')
    e2 = etape('💶', 'Rendement', ('%s %%/an' % fr(rt, 1)) if R.get('calc') else 'n.d.', r_lvl, r_et,
               'seuil %s %% · si ça tourne mal : %s € sur 100 préservés' % (fr(R.get('tx'), 0), fr(R.get('cap_cours'), 0) if num(R.get('cap_cours')) else 'n.d.'))
    e3 = etape('📈', 'Croissance', ('%s %%/an' % fr(gc, 1)) if num(gc) else 'n.d.', _lvl_g(gc), c_et,
               'passé %s · analystes %s' % (('%s %%' % fr(S.get('passe'), 1)) if num(S.get('passe')) else 'n.d.',
                                           ('%s %%' % fr(S.get('consensus'), 1)) if num(S.get('consensus')) else 'n.d.'))
    tm_ = L.get('tm')
    v4 = ('%s exigés<br>%s vus' % (('~%s ans' % fr(tm_, 0)) if num(tm_) else 'n.d.', ('~%s ans' % fr(H, 0)) if num(H) else 'n.d.'))
    e4 = etape('⏳', 'Longévité', '<span style="font-size:22px;line-height:1.3;display:block">%s</span>' % v4, L['lvl'], L['lab'],
               esc(L['txt']) + ' · preuves de durée : %s' % esc(str(L.get('preuve', 'n.d.')).lower()))
    fl = '<div class="gen-f">➜</div>'
    gen = '<div class="gen">%s%s%s%s%s%s%s</div>' % (e1, fl, e2, fl, e3, fl, e4)
    # bandeau des feux
    feux = [('la qualité', f_q), ('le prix', f_r), ('la croissance', f_c), ('la longévité', f_l)]
    n_v = sum(1 for _, f in feux if f)
    manque = [n for n, f in feux if not f]
    def coul(lvl):
        return 'var(--gris)' if lvl == 'gris' or lvl is None else 'var(--l%s)' % lvl
    # V24 : la pastille suit le feu (vert = feu allume), sinon la couleur de l'etape
    pastilles = ''.join('<span class="feu" style="background:%s" title="%s"></span>' % (coul(5 if f else (lv if lv not in (5, 6) else 4)), esc(nom))
                        for nom, f, lv in (('qualité', f_q, qlvl), ('prix', f_r, r_lvl), ('croissance', f_c, _lvl_g(gc)), ('longévité', f_l, L['lvl'])))
    if n_v == 4:
        msg = '4 feux sur 4 : tout est au vert.'
    else:
        msg = '%s %s sur 4 : il manque %s.' % (n_v, 'feux' if n_v > 1 else 'feu', ', '.join(manque[:-1]) + (' et ' if len(manque) > 1 else '') + manque[-1])
    autres = [n_ for n_, e in P.items() if n_ not in ('Qualité', 'Prix', 'Croissance') and e is False]
    if autres:
        msg = msg.replace(' : tout est au vert.', ',') if n_v == 4 else msg
        msg += ' %s l’achat reste bloqué par la porte %s.' % ('mais' if n_v == 4 else 'Et', ', '.join(autres))
    band = '<div class="feux"><div>%s</div><b>🚦 %s</b></div>' % (pastilles, esc(msg))
    # la phrase en clair : le prix suit les portes
    return '%s%s<div class="enclair">%s</div>' % (gen, band, esc(_phrase_prix(D, R)))


# ---------------------------------------------------------------- V23.7.1 : 🌍 ce que l'entreprise apporte au monde
def _items_monde(lst):
    out = []
    for x in (lst if isinstance(lst, list) else []):
        if isinstance(x, str):
            x = [x]
        if not (isinstance(x, list) and x and str(x[0]).strip()):
            continue
        p = _nb(x[1]) if len(x) > 1 else None
        if p not in (1.0, 2.0, 3.0):
            if p is not None:
                warn('monde : poids %r hors de 1-3 pour « %s », lu comme 1.' % (x[1], str(x[0])[:40]))
            p = 1.0
        out.append((str(x[0]).strip(), int(p), str(x[2]).strip() if len(x) > 2 and x[2] else ''))
    return out


def calc_monde(D, R):
    m = D.get('monde') if isinstance(D.get('monde'), dict) else {}
    pos, neg = _items_monde(m.get('positif')), _items_monde(m.get('negatif'))
    P, N = sum(i[1] for i in pos), sum(i[1] for i in neg)
    eth = str((V(G(D, 'profil.ethique'))['v'] or '')).upper()
    out = dict(pos=pos, neg=neg, P=P, N=N, synthese=str(m.get('synthese') or '').strip(), score=None)
    R['monde'] = out
    if not pos and not neg:
        out.update(lab='BALANCE À DOCUMENTER', lvl='gris')
        return
    sc = (P - N) / float(P + N)
    out['score'] = sc
    if sc >= 0.5:
        lab, lvl = 'PENCHE NETTEMENT VERS LE POSITIF', 6
    elif sc >= 0.15:
        lab, lvl = 'PLUTÔT POSITIF', 5
    elif sc > -0.15:
        lab, lvl = 'ÉQUILIBRÉ', 4
    elif sc > -0.5:
        lab, lvl = 'PLUTÔT NÉGATIF', 3
    else:
        lab, lvl = 'PENCHE NETTEMENT VERS LE NÉGATIF', 2
    out.update(lab=lab, lvl=lvl)
    if not neg:
        warn('🌍 Colonne négative vide : toute activité a un coût pour le monde (énergie, déchets, données, addiction, emploi, '
             'gouvernance…). La balance doit chercher l’objection.')
    if sc <= -0.5 and 'CONFORME' in eth:
        warn('🌍 Balance nettement négative mais ligne éthique CONFORME : à trancher.')
    if sc >= 0.5 and 'CONTRAIRE' in eth:
        warn('🌍 Balance nettement positive mais ligne éthique CONTRAIRE À MES VALEURS : à trancher.')
    sans_preuve = [i[0] for i in pos + neg if not i[2]]
    if sans_preuve:
        warn('🌍 %s élément(s) de la balance sans fait ni preuve : %s.' % (len(sans_preuve), '; '.join(x[:40] for x in sans_preuve[:3])))


def balance_svg(M):
    sc = M.get('score')
    ang = -(sc or 0) * 16.0
    W, H, cx, cy, L = 420, 250, 210, 70, 150
    a = math.radians(ang)
    xl, yl = cx - L * math.cos(a), cy - L * math.sin(a)
    xr, yr = cx + L * math.cos(a), cy + L * math.sin(a)
    def plateau(x, y, coul, txt):
        return ('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s" stroke-width="1.5"/>'
                '<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s" stroke-width="1.5"/>'
                '<path d="M%.1f %.1f q48 34 96 0 z" fill="%s" fill-opacity=".22" stroke="%s" stroke-width="2"/>'
                '<text x="%.1f" y="%.1f" fill="%s" font-size="22" font-weight="700" text-anchor="middle" font-family="ui-monospace,monospace">%s</text>') % (
            x, y, x - 48, y + 70, coul, x, y, x + 48, y + 70, coul, x - 48, y + 70, coul, coul, x, y + 62, coul, esc(txt))
    return ('<svg viewBox="0 0 %d %d" role="img" aria-label="Balance positif contre négatif" style="width:100%%;max-width:420px;height:auto;display:block;margin:auto">'
            '<path d="M%d %d L%d %d L%d %d Z" fill="#1d2a2e" stroke="#39d6e0" stroke-width="1.5"/>'
            '<line x1="%d" y1="%d" x2="%d" y2="%d" stroke="#39d6e0" stroke-width="3"/>'
            '<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#e8f2f4" stroke-width="4" stroke-linecap="round"/>'
            '<circle cx="%d" cy="%d" r="7" fill="#39d6e0"/>%s%s</svg>') % (
        W, H, cx - 34, H - 8, cx + 34, H - 8, cx, H - 40, cx, cy, cx, H - 40, xl, yl, xr, yr, cx, cy,
        plateau(xl, yl, '#4ede9a', '+%s' % M['P']), plateau(xr, yr, '#f0605f', '−%s' % M['N']))


def monde_html(R):
    M = R.get('monde') or {}
    if not M:
        return ''
    def liste(items, signe, coul):
        if not items:
            return '<p class="sub">Rien de documenté.</p>'
        return '<ul style="list-style:none;padding:0;margin:0">%s</ul>' % ''.join(
            '<li style="margin:12px 0"><span style="color:%s;font-family:ui-monospace,monospace">%s %s</span> %s%s</li>' % (
                coul, signe, '●' * p + '○' * (3 - p), esc(t), ('<div class="lab" style="margin-top:2px">%s</div>' % esc(pr)) if pr else '')
            for t, p, pr in items)
    return ('<div class="c"><h3>🌍 Ce que l’entreprise apporte au monde</h3>'
            '<div class="grid g3" style="align-items:center">'
            '<div><div class="lab" style="color:var(--l5)">➕ De positif</div>%s</div>'
            '<div style="text-align:center">%s<div style="margin-top:8px">%s</div></div>'
            '<div><div class="lab" style="color:var(--l2)">➖ De négatif</div>%s</div></div>'
            '%s<p class="sub">Poids : ● marginal · ●● notable · ●●● cœur du business. Lecture seulement : aucun effet sur le prix ni le verdict ; '
            'la ligne éthique 🚩 reste ta décision.</p></div>') % (
        liste(M['pos'], '+', 'var(--l5)'), balance_svg(M) if M.get('score') is not None else '',
        bdg(M.get('lab', 'n.d.'), M.get('lvl', 'gris'), 'gros wrap'), liste(M['neg'], '−', 'var(--l2)'),
        ('<p style="margin-top:14px">%s</p>' % esc(M['synthese'])) if M.get('synthese') else '')


def episode(n, titre, accroche):
    return ('<div class="ep"><div class="ep-n">%s</div><h2>%s</h2>%s</div>' % (
        esc(n), esc(titre), ('<p class="ep-c">%s</p>' % esc(accroche)) if accroche else ''))


# ===================================================================== V24.0 : decider
# Le dossier ne s'arrete plus a l'analyse : il dit QUOI FAIRE (ligne detenue ou nouvelle), ouvre une seconde voie
# d'achat tactique (Voie B, revalorisation a 12-18 mois) et met en tete le fait qui explique le prix.
# R3 : la Voie A (verdict, prix d'achat, taux exige, taille, tranches) est inchangee. La Voie B est une decision
# distincte, avec ses propres regles, sa taille plafonnee et sa sortie ecrite ; elle ne modifie aucun calcul de la Voie A.
VOIE_B_HAUSSE_MIN = 30.0   # potentiel minimal vers la valeur prudente, %
VOIE_B_CAP_MIN = 80.0      # capital preserve minimal au cours (plus strict que 60 : on ne fait pas confiance au business)
VOIE_B_Q_MIN = 55.0        # note de qualite plancher
VOIE_B_TAILLE = 2.0        # % du portefeuille, au plus
VOIE_B_PLACES = 4          # places Voie B, au plus, sur 20
VOIE_B_MOIS = 12           # catalyseur attendu dans les 12 mois
VOIE_B_HAUSSE_MAX = 300.0  # V25.1 : au-dela, la valeur prudente est a verifier avant d'ouvrir
VOIE_B_SIGNAL_JOURS = 90   # V25.1 : un signal technique de plus de 90 jours (ou date dans le futur) ne vaut plus


def cap_au_prix(R, P):
    """V25.1 : capital preserve du baissier si l'on achete a P (lecture seule)."""
    Bs, ctx = R.get('_Bs'), R.get('ctx')
    if not (Bs and ctx and num(P) and P > 0):
        return None
    try:
        return cap_preserve(P, Bs, ctx)
    except Exception:  # noqa: BLE001
        return None
DECOTE_CASH_B = {'FRAGILES': 0.75, 'TRÈS FRAGILES': 0.5}  # acces au cash pour le minoritaire, Voie B seulement
CONF_MIN, CONF_MAX = 30, 95


PF_FICHIER = 'NICO_Portefeuille.json'


PREFIXES_PLACE = {'HKEX': '.HK', 'HKG': '.HK', 'SEHK': '.HK', 'TYO': '.T', 'TSE': '.T', 'JPX': '.T', 'LON': '.L', 'LSE': '.L',
                  'ASX': '.AX', 'SHA': '.SS', 'SSE': '.SS', 'SHE': '.SZ', 'SZSE': '.SZ', 'EPA': '.PA', 'AMS': '.AS', 'EBR': '.BR',
                  'STO': '.ST', 'HEL': '.HE', 'OSL': '.OL', 'CPH': '.CO', 'ETR': '.DE', 'XETRA': '.DE', 'FRA': '.DE', 'BIT': '.MI',
                  'BME': '.MC', 'SWX': '.SW', 'TSX': '.TO', 'TSXV': '.V', 'NZX': '.NZ', 'SGX': '.SI', 'KRX': '.KS', 'KOSDAQ': '.KQ',
                  'NASDAQ': '', 'NYSE': '', 'AMEX': '', 'OTC': ''}


def ticker_avec_place(t):
    """V25.1 : « HKEX:327 » -> « 0327.HK » ; « NASDAQ:PYPL » -> « PYPL ». Sans prefixe connu, rendu tel quel."""
    t = str(t or '').strip()
    if ':' in t:
        px, reste = t.split(':', 1)
        sx = PREFIXES_PLACE.get(px.strip().upper())
        reste = reste.strip()
        if sx is not None and '.' not in reste:
            t = reste + sx
        else:
            t = reste
    m = re.fullmatch(r'0*(\d{1,4})\.HK', t, re.I)
    if m:
        t = '%04d.HK' % int(m.group(1))
    return t


def _cle_ticker(t):
    """V24.1 : ticker comparable -- place convertie en suffixe (V25.1), majuscules, zeros de tete retires en Asie."""
    t = ticker_avec_place(t).upper()
    m = re.fullmatch(r'0*(\d+)\.(HK|SS|SZ)', t)
    return ('%s.%s' % (m.group(1), m.group(2))) if m else t


def charger_portefeuille(src=None, chemin=None):
    """V24.1 : registre des lignes detenues, tenu une fois pour toutes (NICO_Portefeuille.json).
    Ordre de recherche : --pf, variable NICO_PF, dossier du JSON, dossier de travail, dossier du moteur."""
    cands = [chemin, os.environ.get('NICO_PF')]
    for d in (os.path.dirname(os.path.abspath(src)) if src else None, os.getcwd(), os.path.dirname(os.path.abspath(__file__))):
        if d:
            cands.append(os.path.join(d, PF_FICHIER))
    for c in cands:
        if c and os.path.isfile(c):
            try:
                with open(c, encoding='utf-8') as f:
                    P = json.load(f)
                if not isinstance(P, dict):
                    raise ValueError('le registre doit être un objet JSON {"maj": ..., "lignes": [...]}')
                L = P.get('lignes')
                if not isinstance(L, list):
                    raise ValueError('« lignes » doit être une liste')
                lignes, incomplet = [], False
                for ligne in L:
                    if not isinstance(ligne, dict) or not any(
                            isinstance(ligne.get(k), str) and ligne[k].strip() for k in ('ticker', 'societe')):
                        incomplet = True
                        continue
                    alias = ligne.get('alias')
                    if alias is not None and not (isinstance(alias, list) and all(isinstance(x, str) for x in alias)):
                        incomplet = True
                        ligne = dict(ligne, alias=[])
                    if _sans_accent(ligne.get('voie')).strip() not in ('', 'a', 'b', 'voie a', 'voie b'):
                        incomplet = True
                    lignes.append(ligne)
                if incomplet:
                    warn('Registre du portefeuille incomplet : certaines entrées ou valeurs sont mal formées. Les places tactiques ne peuvent pas être vérifiées.')
                P['lignes'] = lignes
                P['_incomplet'] = incomplet
                P['_chemin'] = c
                return P
            except Exception as e:  # noqa: BLE001
                warn('Registre du portefeuille illisible (%s) : %s — ligne détenue lue dans le JSON seulement.' % (c, e))
                return None
    return None


def ligne_du_portefeuille(D, PF):
    """La ligne du registre qui correspond a ce dossier (ticker, puis nom de societe), ou None."""
    if not PF:
        return None
    meta = D.get('meta') or {}
    k = _cle_ticker(meta.get('ticker'))
    nom = _sans_accent(meta.get('societe'))
    for l in PF.get('lignes') or []:
        if not isinstance(l, dict):
            continue
        alias = l.get('alias')
        tk = [_cle_ticker(x) for x in [l.get('ticker'), *(alias if isinstance(alias, list) else [])]]
        if k and k in tk:
            return l
    for l in PF.get('lignes') or []:
        if not isinstance(l, dict):
            continue
        n_ = _sans_accent(l.get('societe'))
        if n_ and nom and (n_ == nom or (len(n_) >= 5 and n_ in nom) or (len(nom) >= 5 and nom in n_)):
            return l
    return None


def est_detenue(D, PF=None):
    """V24 : une ligne est detenue si meta.detenue, si le statut de suivi est PF, ou si le mode le dit.
    V24.1 : ou, surtout, si elle figure dans le registre du portefeuille -- le moteur le sait tout seul."""
    meta = D.get('meta') or {}
    st = str(G(D, 'verdict.statut') or '').strip().upper()
    mode = _sans_accent(meta.get('mode'))
    return (bool(meta.get('detenue')) or st == 'PF' or 'reevaluation' in mode or 'detenu' in mode
            or ligne_du_portefeuille(D, PF) is not None)


def _mois_entre(a, b):
    return (b.year - a.year) * 12 + (b.month - a.month) + (b.day - a.day) / 30.0


def _pilier_faible(R):
    """Le pilier le plus faible de la note de qualite (nom, %)."""
    pil = (R.get('q') or {}).get('pil') or {}
    cand = [(p.get('pct'), p.get('lab')) for p in pil.values() if num(p.get('pct'))]
    if not cand:
        return None, None
    pct, lab = min(cand, key=lambda t: t[0])
    return lab, pct


def _premiere_phrase(t, n=160):
    t = str(t or '').strip()
    if not t:
        return ''
    m = re.match(r'(.+?[.!?])(\s|$)', t)
    s = m.group(1) if m else t
    return s if len(s) <= n else s[:n - 1].rstrip() + '…'


def calc_momentum_lecture(D, R):
    """V24 : lecture du momentum avec ce qui est disponible. Le momentum des tranches (R['momentum']) n'est PAS modifie (R3)."""
    mom = D.get('momentum') or {}
    p6, mm = vv(mom.get('perf6m_rel')), vv(mom.get('vs_mm200'))
    cours = vv((D.get('meta') or {}).get('cours'))
    mm200 = cours / (1 + mm / 100.0) if (num(mm) and num(cours) and mm > -100) else None
    morceaux = []
    if num(mm):
        morceaux.append('%s la MM200 (%s %%)' % ('au-dessus de' if mm >= 0 else 'sous', fr(mm, 1, True)))
    if num(p6):
        morceaux.append('perf. relative 6 mois %s %%' % fr(p6, 1, True))
    if num(p6) and num(mm):
        lab = R.get('momentum') or 'INDÉTERMINÉ'
    elif num(mm):
        lab = 'AU-DESSUS DE LA MM200' if mm >= 0 else 'SOUS LA MM200'
    elif num(p6):
        lab = 'SURPERFORMANCE 6 MOIS' if p6 >= 0 else 'SOUS-PERFORMANCE 6 MOIS'
    else:
        lab = 'NON MESURÉ'
    lvl = {'FAVORABLE': 5, 'MIXTE': 4, 'DÉFAVORABLE': 3, 'AU-DESSUS DE LA MM200': 5, 'SOUS LA MM200': 3,
           'SURPERFORMANCE 6 MOIS': 5, 'SOUS-PERFORMANCE 6 MOIS': 3}.get(lab, 'gris')
    R['momentum_lecture'] = dict(lab=lab, lvl=lvl, mm=mm, p6=p6, mm200=mm200,
                                 txt=' · '.join(morceaux) if morceaux else 'aucune mesure de cours fournie')
    rp = G(D, 'resultats.reperes') or {}
    pastilles = []
    for cle, nom in (('bpa_n1', 'BPA vs N−1'), ('bpa_attentes', 'BPA vs attentes'), ('ca_n1', 'CA vs N−1'), ('ca_attentes', 'CA vs attentes')):
        x = vv(rp.get(cle))
        pastilles.append((nom, None if not num(x) else x > 0, x))
    abaissee = R.get('guidance_cas') in ('ALERTE MODÉLISÉE', 'VETO ACTIF', 'IMPACT NON BORNABLE')
    R['pastilles'] = dict(liste=pastilles, abaissee=abaissee,
                          n_ok=sum(1 for _, o, _ in pastilles if o), n_conn=sum(1 for _, o, _ in pastilles if o is not None))


def calc_fait_cle(D, R):
    """V24 : le fait qui explique le prix. Detecte la tresorerie superieure a la capitalisation ; sinon lit lecture.fait_cle."""
    meta, lec = D.get('meta') or {}, D.get('lecture') or {}
    fk = lec.get('fait_cle')
    fk = (list(fk) + ['', '', ''])[:3] if isinstance(fk, list) else [fk or '', '', '']
    tnm, cap = vv(G(D, 'plancher.tresorerie_nette_meur')), vv(meta.get('capitalisation_meur'))
    auto, ve = '', None
    R['ve_negative'] = False
    if num(tnm) and num(cap) and cap > 0:
        ve = cap - tnm
        r = tnm / cap
        if r >= 1:
            R['ve_negative'] = True
            R['ve_verif'] = False
            auto = ('Le marché te vend %s M€ de trésorerie nette pour %s M€ de capitalisation : le business est valorisé à moins de zéro '
                    '(valeur d’entreprise ≈ %s M€).' % (fr(tnm, 0), fr(cap, 0), fr(ve, 0)))
        elif r >= 0.5:
            auto = ('La trésorerie nette couvre %s %% de la capitalisation : le business lui-même ne coûte que %s M€.'
                    % (fr(100 * r, 0), fr(ve, 0)))
    # V25.1 : recouper avec la tresorerie nette PAR ACTION et le cours, a la meme date (la capitalisation declaree peut etre figee)
    tna, cours_ = vv(G(D, 'valo.tresorerie_nette_action')), vv(meta.get('cours'))
    if num(tna) and num(cours_) and cours_ > 0:
        if cours_ <= tna:
            R['ve_negative'], R['ve_verif'] = True, True
        elif R['ve_negative']:
            R['ve_negative'], R['ve_verif'] = False, None
            auto = ''
            warn('Trésorerie nette ≥ capitalisation déclarée, mais le cours (%s) dépasse la trésorerie nette par action (%s) : '
                 'capitalisation à mettre à jour — valeur d’entreprise négative NON retenue.' % (fprix(cours_), fprix(tna)))
    if R.get('ve_negative') and not R.get('ve_verif'):
        warn('Valeur d’entreprise négative calculée sur la capitalisation déclarée seulement : renseigner valo.tresorerie_nette_action pour la recouper.')
    if not auto and num(R.get('mult_exige')) and num(G(D, 'valo.scenarios.central.multiple')):
        mc = G(D, 'valo.scenarios.central.multiple')
        if R['mult_exige'] < 0.6 * mc:
            auto = ('Pour te rapporter ton seuil, le cours n’exige qu’un multiple de sortie de %s×, contre %s× dans notre central : '
                    'le marché prix un scénario bien plus sombre.' % (fr(R['mult_exige'], 1), fr(mc, 1)))
    pd = lec.get('point_decisif') or {}
    fait = str(fk[0]).strip() or auto
    doute = str(fk[1]).strip() or str(pd.get('raison_prix') or '').strip()
    bascule = str(fk[2]).strip() or str(G(D, 'verdict.suivi_condition') or '').strip() or str(lec.get('catalyseur') or '').strip()
    R['fait_cle'] = dict(fait=fait, auto=bool(auto) and not str(fk[0]).strip(), doute=doute,
                         bascule=_premiere_phrase(bascule, 220), ve=ve) if fait else {}
    if R['ve_negative']:
        chk('Fait clé : trésorerie supérieure à la capitalisation', 'alerte',
            'valeur d’entreprise négative : le PER se lit avec prudence, la question devient l’accès au cash')


def calc_asymetrie(D, R):
    """V24 : si j'ai tort / si j'ai raison / esperance ponderee (TRI des flux ponderes du moteur)."""
    out = {}
    R['asymetrie'] = out
    if not R.get('calc') or 'ctx' not in R:
        return
    cours = vv((D.get('meta') or {}).get('cours'))
    scs = G(D, 'valo.scenarios') or {}
    h = scs.get('haussier') if isinstance(scs, dict) else None
    tri_h = val_h = None
    if isinstance(h, dict) and h.get('bpa'):
        try:
            tri_h = tri(flux(cours, h, R['ctx'])[0])
            val_h = val_term(h, R['ctx'])
        except Exception:
            pass
    cc = R.get('cap_cours')
    perte = (cc - 100.0) if num(cc) else None
    fois = (1 + tri_h / 100.0) ** 4 if num(tri_h) else None
    ratio = ((fois - 1) * 100 / abs(perte)) if (num(fois) and num(perte) and perte < -0.5) else None
    out.update(perte=perte, tri_h=tri_h, fois=fois, val_h=val_h, esp=R.get('tri_pondere'), ratio=ratio)
    if num(perte) and num(fois):
        if perte >= -10 and fois >= 2:
            out.update(lab='PILE JE GAGNE, FACE JE PERDS PEU', lvl=6)
        elif num(ratio) and ratio >= 3:
            out.update(lab='ASYMÉTRIE FAVORABLE', lvl=5)
        elif num(ratio) and ratio >= 1.5:
            out.update(lab='ASYMÉTRIE CORRECTE', lvl=4)
        else:
            out.update(lab='PARI SYMÉTRIQUE', lvl=3)
    else:
        out.update(lab='ASYMÉTRIE NON MESURÉE', lvl='gris')


def calc_confiance(D, R):
    """V24 : % de confiance (30-95, jamais 100) -- si j'achete au prix d'achat, le trade delivre-t-il le rendement vise ?
    Convention de selection construite sur un faisceau d'indices, pas une probabilite mesuree. Lecture seule."""
    lec = D.get('lecture') or {}
    dec = lec.get('confiance')
    pts = []
    def add(lib, p):
        if p:
            pts.append((lib, p))
    pm = (R.get('pm') or {}).get('lab', '')
    add('catalyseur daté', 6 if pm == 'CATALYSEUR DATÉ' else 0)
    add('catalyseur probable', 3 if pm == 'CATALYSEUR PROBABLE' else 0)
    add('pari de revalorisation sans catalyseur', -6 if 'PARI DE REVALORISATION' in pm else 0)
    bl = (R.get('boule_neige') or {}).get('lab', '')
    add('boule de neige étayée', 10 if bl == 'BOULE DE NEIGE ÉTAYÉE' else 0)
    add('croissance destructrice ou fragile', -8 if bl in ('CROISSANCE DESTRUCTRICE', 'BOULE DE NEIGE FRAGILE') else 0)
    add('deux confirmations indépendantes', 8 if R.get('preuves_ok') else -5)
    Q = (R.get('q') or {}).get('Q')
    if num(Q):
        add('qualité %s %%' % fr(Q, 0), 8 if Q >= 80 else 4 if Q >= 70 else 0 if Q >= 60 else -6)
    P = R.get('pastilles') or {}
    if P.get('abaissee'):
        add('guidance abaissée', -10)
    elif P.get('n_conn'):
        r = P['n_ok'] / float(P['n_conn'])
        add('trimestre : %s/%s pastilles vertes' % (P['n_ok'], P['n_conn']), 5 if r >= 0.99 else 2 if r >= 0.5 else -4)
    ml = (R.get('momentum_lecture') or {}).get('lvl')
    add('momentum du cours', 4 if ml == 5 else -3 if ml == 3 else 0)
    il = (R.get('init') or {}).get('lab', '')
    add('initiés', 6 if il == 'ACHAT FORT DES INITIÉS' else 2 if il == 'ACHATS LIMITÉS' else -8 if il == 'VENTES FORTES AU PLUS BAS' else 0)
    bb = (R.get('baissier') or {}).get('lab')
    add('baissier', 4 if bb == 'CRÉDIBLE' else -8 if bb == 'DOUTEUX' else 0)
    fi = str((D.get('meta') or {}).get('fiabilite') or 'B').upper()[:1]
    add('fiabilité %s' % fi, {'A': 3, 'C': -5, 'D': -15}.get(fi, 0))
    sl = (R.get('sources_g') or {}).get('lab', '')
    add('central face au consensus', 3 if sl.startswith(('PLUS PRUDENT', 'ALIGNÉ')) else -4 if 'SANS MOTIF' in sl else 0)
    lg = R.get('longevite') or {}
    add('longévité', 4 if lg.get('feu') else -6 if lg.get('lab') == 'PAS CRÉDIBLE' else 0)
    av = (R.get('avenir') or {}).get('lvl')
    add('avenir du besoin', 4 if av in (5, 6) else -6 if av in (1, 2) else 0)
    cpa = R.get('cap_PA')
    add('capital préservé au prix max. d’achat', 3 if (num(cpa) and cpa >= 80) else -5 if (num(cpa) and cpa < 60) else 0)
    brut = 50 + sum(p for _, p in pts)
    pct = max(CONF_MIN, min(CONF_MAX, brut))
    src = 'calculée'
    if isinstance(dec, list) and dec and num(_nb(dec[0])):
        pct = max(CONF_MIN, min(CONF_MAX, _nb(dec[0])))
        src = 'déclarée : ' + (str(dec[1]) if len(dec) > 1 else 'motif non écrit')
        if len(dec) < 2 or not str(dec[1]).strip():
            warn('Confiance déclarée sans motif (lecture.confiance) : écrire le pourquoi.')
    lvl = 6 if pct >= 80 else 5 if pct >= 65 else 4 if pct >= 50 else 3 if pct >= 40 else 2
    R['confiance'] = dict(pct=pct, brut=brut, pts=pts, src=src, lvl=lvl)


def these_tactique_invalidee(D):
    """True = stop confirmé, None = format à corriger, False = pas de déclenchement déclaré."""
    flags = (G(D, 'voie_b.these_invalidee'), G(D, 'lecture.these_invalidee'))
    if any(x is True for x in flags):
        return True
    return None if any(x is not None and x is not False for x in flags) else False


def calc_voie_b(D, R):
    """V24 : Voie B -- opportunite de revalorisation a 12-18 mois, pour une societe qui ne merite pas la Voie A
    (garder 3-5 ans) mais dont le prix, un catalyseur date et le cours lui-meme annoncent une revalorisation.
    Sept regles, une sortie ecrite le jour de l'achat. Aucun effet sur la Voie A (R3)."""
    meta, valo = D.get('meta') or {}, D.get('valo') or {}
    vb = D.get('voie_b') if isinstance(D.get('voie_b'), dict) else {}
    cours = vv(meta.get('cours'))
    dev = meta.get('devise', '')
    vf = str(R.get('verdict_final') or '').upper()
    out = dict(tests=[], statut='', lab='', lvl='gris', txt='')
    R['voie_b'] = out
    PF = R.get('pf') or {}
    if PF.get('tactique_ligne'):
        out.update(statut='EN SUIVI', lab='VOIE B EN SUIVI', txt='le plan de sortie est celui du registre')
        return
    if not R.get('calc'):
        out.update(statut='NON ÉVALUÉE', lab='VOIE B NON ÉVALUÉE', txt='valorisation non exécutée')
        return
    if vf.startswith(('ACHAT', 'RENFORCEMENT')):
        out.update(statut='SANS OBJET', lab='VOIE A OUVERTE', lvl=5,
                   txt='la société mérite une place durable : l’achat standard (Voie A) s’applique')
        return
    T = out['tests']
    # 0. V25.1 : les blocages qui invalident le dossier valent aussi pour la Voie B
    P0 = dict(R.get('portes') or [])
    blq = []
    if 'REJET' in vf: blq.append('verdict %s' % vf.lower())
    if 'PÉRIMÈTRE' in vf or 'PERIMETRE' in vf: blq.append('hors périmètre')
    if P0.get('Unités') is False: blq.append('unités incohérentes')
    if P0.get('Ancrage') is False or (R.get('calc') and not R.get('valorisation_valide', True)): blq.append('ancrage terminal à corriger')
    T.append(('Dossier recevable', not blq, ' ; '.join(blq) if blq else 'ni rejet, ni hors périmètre, unités et ancrage validés'))
    # 1. decote prouvee, sans BPA futur
    vp_d = V(vb.get('valeur_prudente'))
    if num(_nb(vp_d['v'])):
        vp = _nb(vp_d['v'])
        vp_src = 'déclarée%s' % ((' : ' + str(vp_d['src'] or vp_d['note'])) if (vp_d['src'] or vp_d['note']) else '')
        vp_sans_methode = not all(isinstance(vp_d[k], str) and vp_d[k].strip() for k in ('src', 'note'))
        if vp_sans_methode:
            warn('Voie B : valeur prudente déclarée sans méthode (voie_b.valeur_prudente) — écrire la méthode et la source.')
    else:
        tn, base = vv(valo.get('tresorerie_nette_action')), vv(valo.get('base_normalisee'))
        pf = vv(valo.get('produit_financier_action')) or 0.0
        mb = G(D, 'valo.scenarios.baissier.multiple')
        droits = str(V(G(D, 'taux_exige.droits_actionnaire'))['v'] or '').upper()
        fac = next((f for k, f in sorted(DECOTE_CASH_B.items(), key=lambda kv: -len(kv[0])) if k in droits), 1.0)
        if num(base) and num(mb) and base - pf > 0:
            vp = (tn * fac if num(tn) else 0.0) + (base - pf) * mb
            vp_src = ('BPA normalisé d’exploitation %s × multiple baissier %s×%s' % (
                fr(base - pf, 2), fr(mb, 2),
                (' + trésorerie nette %s%s' % (fprix(tn), (' comptée à %s %% (droits %s)' % (fr(100 * fac, 0), droits.lower())) if fac < 1 else ''))
                if num(tn) else ''))
        else:
            vp, vp_src = None, 'base normalisée ou multiple baissier manquant'
    hausse = 100 * (vp / cours - 1) if (num(vp) and num(cours) and cours > 0) else None
    if num(_nb(vp_d['v'])) and vp_sans_methode:
        T.append(('Décote prouvée', None, 'valeur prudente %s %s déclarée sans méthode : écrire la méthode et la source' % (fprix(vp), dev)))
    elif num(hausse) and hausse > VOIE_B_HAUSSE_MAX:
        T.append(('Décote prouvée', None, 'potentiel de %s %% vers %s %s : trop beau pour être pris tel quel, vérifier la valeur prudente'
                  % (fr(hausse, 0, True), fprix(vp), dev)))
    else:
      T.append(('Décote prouvée', None if not num(hausse) else hausse >= VOIE_B_HAUSSE_MIN,
                ('valeur prudente %s %s, soit %s %% de potentiel (il faut ≥ %s %%) — %s' % (
                    fprix(vp), dev, fr(hausse, 0, True), fr(VOIE_B_HAUSSE_MIN, 0), vp_src)) if num(hausse) else vp_src))
    # 2. catalyseur date a 12 mois
    pm = R.get('pm') or {}
    d0 = _date(meta.get('date_eval'))
    ech_src = [(vb.get('echeance'), 'échéance Voie B'), (pm.get('date'), 'date du catalyseur'), (G(D, 'verdict.suivi_date'), 'échéance de suivi')]
    ech, ech_lib = None, ''
    for x, lib in ech_src:
        e = _date(x)
        if e:
            ech, ech_lib = e, lib
            break
    mois = _mois_entre(d0, ech) if (d0 and ech) else None
    c_ok = None
    if pm.get('lab') in ('CATALYSEUR DATÉ', 'CATALYSEUR PROBABLE') and not str(pm.get('fait') or '').strip():
        c_ok, c_txt = None, '%s sans fait décrit : écrire le fait vérifiable et sa date (lecture.pourquoi_maintenant)' % pm['lab'].lower()
    elif pm.get('lab') in ('CATALYSEUR DATÉ', 'CATALYSEUR PROBABLE'):
        c_ok = bool(num(mois) and 0 < mois <= VOIE_B_MOIS)
        c_txt = '%s — %s%s' % (pm['lab'].lower(), _premiere_phrase(pm.get('fait'), 140),
                               (' · %s %s (dans %s mois)' % (ech_lib, ech.strftime('%d/%m/%Y'), fr(mois, 0))) if num(mois) else ' · aucune échéance datée')
    else:
        c_ok, c_txt = False, 'aucun catalyseur identifié (%s) : sans catalyseur, le prix bas peut durer' % (pm.get('lab') or 'non documenté').lower()
    T.append(('Catalyseur à ≤ %s mois' % VOIE_B_MOIS, c_ok, c_txt))
    # 3. le cours confirme
    ML = R.get('momentum_lecture') or {}
    sig = vb.get('signal_technique')
    sig = (list(sig) + ['', '', ''])[:3] if isinstance(sig, list) else None
    sig_ok = bool(sig and str(sig[0]).strip() and str(sig[1]).strip() and _date(sig[2]))
    sig_note = ''
    if sig_ok and d0:
        age = (d0 - _date(sig[2])).days
        if age < 0 or age > VOIE_B_SIGNAL_JOURS:
            sig_ok = False
            sig_note = ' (signal du %s ignoré : %s)' % (sig[2], 'daté après l’évaluation' if age < 0 else 'plus de %s jours, périmé' % VOIE_B_SIGNAL_JOURS)
    mm = ML.get('mm')
    if sig_ok:
        p_ok, p_txt = True, 'signal technique : %s — %s (%s)' % (sig[0], sig[1], sig[2])
    elif num(mm):
        p_ok = mm >= 0
        p_txt = 'cours %s la moyenne 200 jours (%s %%)%s%s' % ('au-dessus de' if p_ok else 'sous', fr(mm, 1, True),
                                                             '' if p_ok else ' : déclencheur au-dessus de %s %s' % (fprix(ML.get('mm200')), dev), sig_note)
    else:
        p_ok, p_txt = None, 'écart à la MM200 non fourni (momentum.vs_mm200) et aucun signal technique valide (voie_b.signal_technique)' + sig_note
    T.append(('Le cours confirme', p_ok, p_txt))
    # 4. le trimestre confirme, guidance non abaissee
    P = R.get('pastilles') or {}
    l = {n: o for n, o, _ in P.get('liste') or []}
    if P.get('abaissee'):
        t_ok, t_txt = False, 'guidance abaissée : le momentum fondamental est annulé (règle du 20/07)'
    elif l.get('CA vs N−1') is None and l.get('BPA vs N−1') is None:
        t_ok, t_txt = None, 'derniers résultats non renseignés (resultats.reperes)'
    else:
        t_ok = bool(l.get('CA vs N−1')) and bool(l.get('BPA vs N−1'))
        t_txt = '%s/%s pastilles vertes · CA et BPA %s l’an passé' % (P.get('n_ok', 0), P.get('n_conn', 0), 'au-dessus de' if t_ok else 'pas tous deux au-dessus de')
    T.append(('Le trimestre confirme', t_ok, t_txt))
    # 5. capital preserve
    cc = R.get('cap_cours')
    T.append(('Capital préservé ≥ %s/100' % fr(VOIE_B_CAP_MIN, 0), None if not num(cc) else cc >= VOIE_B_CAP_MIN,
              'au cours : %s/100 si le baissier arrive' % fr(cc, 0)))
    # 6. qualite plancher
    q_ = R.get('q') or {}
    Q = q_.get('Q')
    if num(Q) and (q_.get('provisoire') or (num(q_.get('cov')) and q_['cov'] < 80)):
        T.append(('Qualité ≥ %s %%' % fr(VOIE_B_Q_MIN, 0), None, 'note %s %% provisoire (couverture %s %% des contrôles) : compléter la grille'
                  % (fr(Q, 0), fr(q_.get('cov'), 0))))
    else:
        T.append(('Qualité ≥ %s %%' % fr(VOIE_B_Q_MIN, 0), None if not num(Q) else Q >= VOIE_B_Q_MIN, 'note %s %%' % fr(Q, 0)))
    # 7. comptes fiables
    fi = str(meta.get('fiabilite') or 'B').upper()[:1]
    fo = ((R.get('profil') or {}).get('forensique') or {})
    pb = []
    if fi == 'D': pb.append('fiabilité D')
    if (D.get('qualite') or {}).get('blocage'): pb.append('blocage structurel')
    if (R.get('baissier') or {}).get('lab') == 'DOUTEUX': pb.append('baissier douteux')
    if len(fo.get('alertes') or []) >= 2: pb.append('double alerte forensique')
    T.append(('Comptes fiables', not pb, ' ; '.join(pb) if pb else 'fiabilité %s, aucun blocage, baissier non douteux, pas de double alerte forensique' % fi))
    # 8. V25.1 : la sortie s'ecrit avant d'entrer
    inv_brut = G(D, 'lecture.invalidation')
    inv = _premiere_phrase(inv_brut, 200) if isinstance(inv_brut, str) else ''
    stop = these_tactique_invalidee(D)
    T.append(('Stop thèse', False if stop is True else (True if stop is False and inv else None),
              'thèse déjà invalidée' if stop is True else 'these_invalidee doit être un booléen JSON' if stop is None else
              inv or 'lecture.invalidation absent : écrire le stop avant d’entrer'))
    # 9. V25.1 : quatre places tactiques au plus (registre du portefeuille)
    tac = PF.get('tactiques')
    places_connues = num(tac) and (not R.get('detenue') or bool(PF.get('ligne')))
    T.append(('Place tactique libre', tac < VOIE_B_PLACES if places_connues else None,
              '%s place(s) Voie B occupée(s) sur %s dans le registre' % (int(tac), VOIE_B_PLACES) if places_connues else
              'registre absent, incomplet ou en conflit avec la détention : vérifier les places avant tout ordre tactique'))
    # statut
    echecs = [n for n, o, _ in T if o is False]
    inconnus = [n for n, o, _ in T if o is None]
    if not echecs and not inconnus:
        statut, lab, lvl = 'OUVERTE', 'VOIE B OUVERTE — ACHAT TACTIQUE POSSIBLE', 5
        txt = 'toutes les règles sont réunies : position de %s %% au plus, sortie écrite ci-dessous' % fr(VOIE_B_TAILLE, 0)
    elif echecs == ['Le cours confirme'] and all(n == 'Place tactique libre' for n in inconnus):
        statut, lab, lvl = 'EN ATTENTE', 'VOIE B EN ATTENTE DU SIGNAL', 4
        txt = 'tout est prêt sauf le cours : %s' % next(t for n, _, t in T if n == 'Le cours confirme')
    elif not echecs:
        statut, lab, lvl = 'À DOCUMENTER', 'VOIE B À DOCUMENTER', 'gris'
        txt = 'à documenter : ' + ', '.join(inconnus).lower()
    else:
        statut, lab, lvl = 'FERMÉE', 'VOIE B FERMÉE', 2
        txt = 'règle(s) non remplie(s) : ' + ', '.join(echecs).lower()
    # V25.1 : zone d'entree -- le plus haut prix ou potentiel ET capital preserve tiennent encore
    plaf, p80 = None, None
    Bs, ctx = R.get('_Bs'), R.get('ctx')
    if Bs and ctx and num(cours):
        try:
            p80 = prix_plancher(Bs, ctx, cours * 20, VOIE_B_CAP_MIN)
        except Exception:  # noqa: BLE001
            p80 = None
    if num(vp):
        plaf = vp / (1 + VOIE_B_HAUSSE_MIN / 100.0)
        if num(p80):
            plaf = min(plaf, p80)
    dec = ML.get('mm200') if (statut == 'EN ATTENTE' and num(ML.get('mm200'))) else None
    au_sig = {}
    if num(dec):
        au_sig = dict(prix=dec, hausse=100 * (vp / dec - 1) if num(vp) else None,
                      cap=cap_au_prix(R, dec))
        if num(plaf) and dec > plaf + 1e-9:
            statut, lab, lvl = 'HORS ZONE', 'VOIE B : SIGNAL HORS ZONE D’ACHAT', 3
            txt = ('le signal (%s %s, MM200) arriverait au-dessus du plafond d’entrée de %s %s : à ce prix, le potentiel tomberait à %s %% '
                   'et le capital préservé à %s/100. L’alerte sert à relancer l’analyse, pas à acheter' % (
                       fprix(dec), dev, fprix(plaf), dev, fr(au_sig.get('hausse'), 0, True), fr(au_sig.get('cap'), 0)))
        if not places_connues:
            txt += ' Le registre reste à vérifier avant tout ordre.'
    out.update(statut=statut, lab=lab, lvl=lvl, txt=txt, vp=vp, vp_src=vp_src, hausse=hausse, ech=ech, mois=mois,
               declencheur=dec, plafond=plaf, p80=p80, au_signal=au_sig,
               places_verifiees=places_connues,
               sortie_objectif=vp, sortie_temps=(ech.strftime('%d/%m/%Y') if ech else None), sortie_these=inv)
    chk('Voie B — opportunité de revalorisation (V24)', 'validé' if statut in ('OUVERTE', 'EN ATTENTE', 'FERMÉE', 'HORS ZONE') else 'n.d.', lab)


def calc_action(D, R):
    """V24 : la decision du jour, en clair. Ligne detenue : garder / renforcer / alleger / vendre, d'apres ta regle
    d'arbitrage (rendement attendu au cours - taux exige) et les portes. Nouvelle position : acheter / attendre / ne pas acheter."""
    meta = D.get('meta') or {}
    dev = meta.get('devise', '')
    vf = str(R.get('verdict_final') or '').upper()
    tx, rt = R.get('tx'), R.get('retenu')
    Q = (R.get('q') or {}).get('Q')
    cc = R.get('cap_cours')
    B = R.get('voie_b') or {}
    det = R.get('detenue')
    ecart = (rt - tx) if (num(rt) and num(tx)) else None
    tl = R.get('taille') or {}
    pos = vv(meta.get('position_pct'))
    ordre = ''
    P = dict(R.get('portes') or [])
    fermees = [n for n, e in P.items() if e is False]
    fl, fp = _pilier_faible(R)
    def bloque():
        out = []
        if 'Qualité' in fermees:
            out.append('porte qualité fermée (%s %%%s)' % (fr(Q, 0), (' — point faible : %s %s %%' % (fl.lower(), fr(fp, 0))) if fl else ''))
        if 'Preuves' in fermees:
            out.append('preuves : %s' % (R.get('preuves_motif') or 'confirmations insuffisantes'))
        for n in fermees:
            if n not in ('Qualité', 'Preuves', 'Prix'):
                out.append('porte %s fermée' % n.lower())
        return out
    b_txt = ''
    taille_b_ok = not (det and num(pos) and pos >= VOIE_B_TAILLE)
    if B.get('statut') == 'OUVERTE':
        b_txt = ('ouverte : %s %s %% au plus, objectif %s %s.' % ('ligne plafonnée à' if det else 'achat tactique de', fr(VOIE_B_TAILLE, 0), fprix(B.get('vp')), dev)
                 if taille_b_ok else 'ouverte, mais ta ligne (%s %%) a déjà la taille tactique de %s %% : pas de renfort.' % (fr(pos, 1), fr(VOIE_B_TAILLE, 0)))
    elif B.get('statut') == 'EN ATTENTE' and num(B.get('declencheur')):
        if not taille_b_ok:
            b_txt = 'en attente du signal, mais ta ligne (%s %%) a déjà la taille tactique de %s %% : le signal ne changera rien.' % (fr(pos, 1), fr(VOIE_B_TAILLE, 0))
        else:
            b_txt = ('alerte à %s %s (MM200) : s’il y remonte, relancer le dossier ; renfort tactique seulement si tout tient encore à ce prix '
                     '(plafond d’entrée %s %s), ligne plafonnée à %s %% au total.' if det else
                     'alerte à %s %s (MM200) : s’il y remonte, relancer le dossier ; achat tactique seulement si tout tient encore à ce prix '
                     '(plafond d’entrée %s %s), %s %% au plus.') % (fprix(B['declencheur']), dev, fprix(B.get('plafond')), dev, fr(VOIE_B_TAILLE, 0))
    elif B.get('statut') == 'HORS ZONE':
        b_txt = ('signal hors zone d’achat : la MM200 (%s %s) est au-dessus du plafond d’entrée (%s %s). Alerte à la MM200 = relancer l’analyse, pas %s.'
                 % (fprix(B.get('declencheur')), dev, fprix(B.get('plafond')), dev, 'renforcer' if det else 'acheter'))
    TL = (R.get('pf') or {}).get('tactique_ligne') or {}
    lpf = (R.get('pf') or {}).get('ligne') or {}
    poids_registre = _nb(lpf.get('poids_pct'))
    cours = vv(meta.get('cours'))
    cours_invalide = bool(R.get('unites_suspectes')) or (num(cours) and cours <= 0)
    dossier_a_corriger = cours_invalide or (R.get('calc') and not R.get('valorisation_valide'))
    registre_a_verifier = B.get('statut') == 'À DOCUMENTER' and [
        n for n, ok, _ in B.get('tests', []) if ok is not True] == ['Place tactique libre']
    sortie_b = None
    plan_tactique = ''
    plan_incomplet = False
    if det and TL:  # V25.1 : une ligne ouverte en Voie B se suit avec sa sortie ecrite le jour de l'achat
        obj = _nb(TL.get('objectif'))
        obj = obj if num(obj) and obj > 0 else None
        ech_ = _date(TL.get('echeance'))
        d0_ = _date(meta.get('date_eval'))
        stop_these = TL.get('stop_these')
        stop_these = stop_these.strip() if isinstance(stop_these, str) else ''
        inval = these_tactique_invalidee(D)
        plan_incomplet = not (num(obj) and ech_ and stop_these)
        plan_tactique = 'objectif %s · échéance %s · stop thèse %s' % (
            ('%s %s' % (fprix(obj), dev)) if num(obj) else 'à vérifier',
            ech_.strftime('%d/%m/%Y') if ech_ else 'à vérifier', stop_these or 'à vérifier')
        if plan_incomplet:
            warn('Plan tactique incomplet dans le registre : vérifier l’objectif positif, l’échéance et le stop thèse d’origine.')
        if inval is None:
            warn('these_invalidee doit être un booléen JSON (true ou false) : stop thèse à vérifier.')
        if inval is True and stop_these:
            sortie_b = ('SORTIR — STOP THÈSE', 'le stop thèse écrit à l’achat est déclenché%s' % (
                (' : ' + _premiere_phrase(stop_these, 160)) if stop_these else ''))
        elif num(obj) and num(cours) and cours >= obj and not cours_invalide:
            sortie_b = ('SORTIR — OBJECTIF ATTEINT', 'le cours (%s %s) a atteint l’objectif tactique de %s %s' % (fprix(cours), dev, fprix(obj), dev))
        elif ech_ and d0_ and d0_ > ech_:
            sortie_b = ('SORTIR — STOP TEMPS', 'l’échéance tactique du %s est passée' % ech_.strftime('%d/%m/%Y'))
    if det and sortie_b:
        act, lvl, pq = sortie_b[0], 2, sortie_b[1]
    elif dossier_a_corriger:
        act, lvl = 'DOSSIER À CORRIGER', 'gris'
        pq = R.get('unites_suspectes') or ('cours non positif' if cours_invalide else 'ancrage terminal à corriger')
    elif det:
        if 'PÉRIMÈTRE' in vf or 'PERIMETRE' in vf:
            act, lvl, pq = 'VENDRE', 1, 'la société est sortie de ton périmètre d’investissement'
        elif 'REJET' in vf or (not TL and num(Q) and Q < 55):
            act, lvl = 'VENDRE', 1
            pq = 'la qualité (%s %%) ou la structure ne justifie plus une place parmi tes 20' % fr(Q, 0)
        elif TL:
            if plan_incomplet or inval is None:
                act, lvl, pq = 'VÉRIFIER LE PLAN TACTIQUE', 'gris', 'vérifie le plan d’origine ou le signal d’invalidation avant toute décision'
            elif vf.startswith(('ACHAT', 'RENFORCEMENT')) and num(ecart) and ecart >= 0:
                act, lvl = 'GARDER — CHANGEMENT DE VOIE À VALIDER', 4
                pq = 'la Voie A est ouverte. Garde le plan tactique jusqu’à validation du passage en Voie A dans le registre'
            else:
                act, lvl, pq = 'GARDER — SUIVI TACTIQUE', 4, 'continue de suivre le plan écrit au moment de l’achat'
        elif not R.get('calc'):
            act, lvl, pq = 'GARDER — RÉÉVALUATION INCOMPLÈTE', 'gris', 'valorisation non exécutée : aucun arbitrage possible'
        elif num(ecart) and ecart < -10:
            act, lvl = 'VENDRE (ARBITRAGE)', 2
            pq = 'rendement attendu %s %%/an, %s pts sous ton seuil : cette place finance une meilleure idée%s' % (
                fr(rt, 1), fr(-ecart, 0), (' ; et au cours, le baissier coûterait plus de 40 %% (capital préservé %s/100)' % fr(cc, 0))
                if (num(cc) and cc < CAP_MIN) else '')
        elif num(cc) and cc < CAP_MIN:
            act, lvl = 'ALLÉGER', 3
            pq = 'au cours du jour, le baissier coûterait plus de 40 %% (capital préservé %s/100)' % fr(cc, 0)
        elif num(ecart) and ecart < -5:
            act, lvl = 'ALLÉGER', 3
            pq = 'rendement attendu %s %%/an, %s pts sous ton seuil' % (fr(rt, 1), fr(-ecart, 0))
        elif num(ecart) and ecart < 0:
            act, lvl = 'GARDER, NE PAS RENFORCER', 4
            pq = 'rendement attendu %s %%/an, juste sous ton seuil de %s %%' % (fr(rt, 1), fr(tx, 0))
        elif R.get('guidance_cas') == 'VETO ACTIF':
            act, lvl, pq = 'GARDER SOUS SURVEILLANCE', 3, 'veto de guidance actif : attendre la publication qui confirme la nouvelle base'
        elif vf.startswith(('ACHAT', 'RENFORCEMENT')) and num(pos) and num(tl.get('max')) and pos >= tl['max'] - 0.05:
            act, lvl = 'GARDER — TAILLE ATTEINTE', 5
            pq = 'tout est au vert, mais ta ligne (%s %%) atteint déjà la taille maximale de %s %%' % (fr(pos, 1), fr(tl['max'], 1))
        elif vf.startswith(('ACHAT', 'RENFORCEMENT')):
            act, lvl = 'RENFORCER', 6
            pq = 'rendement attendu %s %%/an pour un seuil de %s %% et toutes les portes ouvertes' % (fr(rt, 1), fr(tx, 0))
            if num(tl.get('max')):
                ordre = 'jusqu’à %s %% du portefeuille%s, au plus %s %s' % (fr(tl['max'], 1), (' (aujourd’hui %s %%)' % fr(pos, 1)) if num(pos) else '',
                                                                       fprix(R.get('PA')), dev)
        else:
            act, lvl = 'GARDER, NE PAS RENFORCER', 4
            pq = ('le prix paie (%s %%/an pour un seuil de %s %%, %s pts d’avance), mais %s'
                  % (fr(rt, 1), fr(tx, 0), fr(ecart, 0, True), ' ; '.join(bloque()) or 'le verdict reste bloquant'))
        if (act == 'GARDER, NE PAS RENFORCER' and num(ecart) and ecart >= 0 and B.get('statut') == 'OUVERTE'
                and num(poids_registre) and 0 < poids_registre < VOIE_B_TAILLE):
            act, lvl = 'RENFORCER TACTIQUEMENT (VOIE B)', 5
            pq = pq + ' ; la Voie B est ouverte : renfort tactique permis'
            ordre = 'porter la ligne de %s %% à %s %% au plus, sous %s %s · objectif %s %s · stop temps %s · stop thèse écrit' % (
                fr(pos, 1), fr(VOIE_B_TAILLE, 0), fprix(B.get('plafond')), dev, fprix(B.get('vp')), dev, B.get('sortie_temps') or 'n.d.')
            b_txt = ''
        elif act == 'GARDER, NE PAS RENFORCER' and registre_a_verifier:
            act, lvl, pq = 'VÉRIFIER LE REGISTRE', 'gris', 'vérifie les places et le poids de ta ligne avant tout renfort tactique'
        elif act == 'GARDER, NE PAS RENFORCER' and B.get('statut') == 'OUVERTE' and not (
                num(poids_registre) and 0 < poids_registre <= 100):
            act, lvl, pq = 'VÉRIFIER LE REGISTRE', 'gris', 'renseigne un poids valide dans le registre avant tout renfort tactique'
            b_txt = ''
        if num(ecart) and not TL and act != 'VÉRIFIER LE REGISTRE':
            ordre = ordre or ('arbitrage trimestriel : %s pts %s ton seuil de %s %%' % (
                fr(abs(ecart), 1), 'd’avance sur' if ecart >= 0 else 'de retard sur', fr(tx, 0)))
    else:
        if vf.startswith(('ACHAT', 'RENFORCEMENT')):
            act, lvl = 'ACHETER', 6
            pq = 'toutes les portes sont ouvertes et le cours est sous le prix maximum d’achat'
            ordre = 'tranche 1 (%s) à %s %s au plus · taille %s' % (R.get('tranches') or 'n.d.', fprix(R.get('PA')), dev, taille_txt(R))
        elif B.get('statut') == 'OUVERTE':
            act, lvl = 'ACHAT TACTIQUE (VOIE B)', 5
            pq = 'pas une société à garder des années, mais un prix, un catalyseur et un cours qui annoncent une revalorisation'
            ordre = '%s %% du portefeuille au plus, sous %s %s · vendre à %s %s, au %s au plus tard, ou si le stop thèse tombe' % (
                fr(VOIE_B_TAILLE, 0), fprix(B.get('plafond')), dev, fprix(B.get('vp')), dev, B.get('sortie_temps') or 'n.d.')
        elif 'PRIX' in vf:
            act, lvl = 'ATTENDRE LE PRIX', 4
            pq = 'bonne société, prix trop élevé : %s %%/an au cours pour un seuil de %s %%' % (fr(rt, 1), fr(tx, 0))
            ordre = 'alerte à %s %s (prix maximum d’achat), puis relancer le dossier' % (fprix(R.get('PA')), dev) if num(R.get('PA')) else ''
        elif 'CONFIRMATION' in vf or 'GUIDANCE' in vf:
            act, lvl = 'ATTENDRE LA CONFIRMATION', 4
            pq = '; '.join(R.get('verdict_motifs') or []) or 'confirmations insuffisantes'
        elif B.get('statut') == 'EN ATTENTE':
            act, lvl = 'ATTENDRE LE SIGNAL (VOIE B)', 4
            pq = 'trop fragile pour la garder des années (%s), mais candidate à un achat tactique dès que le cours confirme' % (
                ' ; '.join(bloque()) or vf.lower())
            ordre = ('alerte de cours à %s %s (MM200), puis relancer le dossier · plafond d’entrée %s %s · %s %% au plus' % (
                fprix(B.get('declencheur')), dev, fprix(B.get('plafond')), dev, fr(VOIE_B_TAILLE, 0))) if num(B.get('declencheur')) else ''
        elif B.get('statut') == 'FERMÉE' and [n for n, o, _ in B.get('tests') or [] if o is not True] == ['Place tactique libre']:
            act, lvl = 'PAS DE PLACE TACTIQUE', 3
            pq = 'la Voie B serait ouverte, mais tes %s places tactiques sont occupées' % VOIE_B_PLACES
            ordre = 'attendre qu’une place se libère, puis relancer le dossier'
        elif B.get('statut') == 'HORS ZONE':
            act, lvl = 'SURVEILLER (VOIE B HORS ZONE)', 3
            pq = 'candidate à un achat tactique, mais le signal du marché arriverait au-dessus du prix où la Voie B tient encore'
            ordre = 'alerte à %s %s pour relancer l’analyse (plafond d’entrée aujourd’hui %s %s)' % (
                fprix(B.get('declencheur')), dev, fprix(B.get('plafond')), dev)
        elif registre_a_verifier:
            act, lvl, pq = 'VÉRIFIER LE REGISTRE', 'gris', 'vérifie les places disponibles avant tout achat tactique'
        elif 'DOCUMENTER' in vf:
            act, lvl, pq = 'DOCUMENTER AVANT D’ACHETER', 'gris', '; '.join(R.get('verdict_motifs') or []) or 'intrant décisif manquant'
        else:
            act, lvl = 'NE PAS ACHETER', 2
            pq = ' ; '.join(bloque()) or (vf.lower() or 'verdict bloquant')
    if act in ('ACHAT TACTIQUE (VOIE B)', 'ATTENDRE LE SIGNAL (VOIE B)', 'SURVEILLER (VOIE B HORS ZONE)', 'RENFORCER TACTIQUEMENT (VOIE B)') \
            or act.startswith(('VENDRE', 'ALLÉGER', 'SORTIR')):
        b_txt = ''  # deja dans l'action et l'ordre ; une vente prime sur toute idee tactique
    if B.get('statut') in ('EN ATTENTE', 'HORS ZONE') and not B.get('places_verifiees'):
        rappel_registre = 'Vérifie le registre avant tout ordre tactique.'
        if b_txt:
            b_txt += ' ' + rappel_registre
        elif act in ('ATTENDRE LE SIGNAL (VOIE B)', 'SURVEILLER (VOIE B HORS ZONE)'):
            ordre += ' · ' + rappel_registre
    v = D.get('verdict') or {}
    rdv = v.get('suivi_date') or ''
    lec = D.get('lecture') or {}
    voy = lec.get('voyants')
    voyants = []
    if isinstance(voy, list) and voy:
        for x in voy[:3]:
            voyants.append(' · '.join(str(y) for y in x if y) if isinstance(x, list) else str(x))
    else:
        for r_ in (G(D, 'risques.registre') or [])[:3]:
            if isinstance(r_, dict) and r_.get('indicateur'):
                voyants.append(_premiere_phrase(r_['indicateur'], 150))
    R['action'] = dict(act=act, lvl=lvl, pourquoi=pq, ordre=ordre, voie_b=b_txt, detenue=det, pos=pos,
                       rdv=rdv if not TL else '', rdv_txt=_premiere_phrase(v.get('suivi_condition') or lec.get('catalyseur'), 200) if not TL else '',
                       voyants=voyants, plan_tactique=plan_tactique, dossier_a_corriger=bool(dossier_a_corriger), cours_invalide=cours_invalide)
    act_txt = str(lec.get('action') or '')
    if det and re.search(r'n.est pas trait', act_txt):
        warn('Ligne détenue : le texte d’action dit que la conservation n’est pas traitée — le moteur V24 la traite désormais '
             '(bandeau « Que faire ») ; réécrire lecture.action pour la ligne détenue.')


def calc_angles_morts(D, R):
    """V24 : ce que le dossier n'a pas pu verifier, et si ca peut changer la decision. Remplace les blocs vides."""
    am = []
    def add(quoi, change, comment):
        am.append((quoi, change, comment))
    fo = ((R.get('profil') or {}).get('forensique') or {})
    if fo.get('absents'):
        add('Forensique : ' + ', '.join(fo['absents']), 'OUI, si alerte',
            'une double alerte abaisserait la fiabilité et fermerait la Voie B ; Sloan calculable depuis les comptes (risques.forensique.sloan_entrees)')
    if not (R.get('valeur') or {}).get('doc'):
        add('Création de valeur (spread, EVA)', 'NON', 'lecture du profit économique ; la rentabilité est déjà notée par la série ROIC')
    S7 = R.get('sources_g') or {}
    if not num(S7.get('consensus')):
        add('Consensus des analystes', 'NON', 'repère de prudence du central ; ne déplace ni le prix ni le verdict')
    if not num(G(D, 'secteur.s_bas')) and not num(G(D, 'secteur.s_haut')):
        add('Vent sectoriel chiffré', 'NON', 'contexte de la demande ; la trajectoire est jugée sur les moteurs de la société')
    if R.get('calc') and not num(R.get('part_mult')):
        add('Part du multiple dans le TRI', 'OUI, si > 50 %',
            'non calculable quand le cash dépasse ce que vaut le business au cours' if R.get('ve_negative') else 'au-delà de 50 %, l’achat devient un pari de revalorisation')
    if not num(G(D, 'momentum.perf6m_rel')):
        add('Performance relative 6 mois', 'RYTHME', 'règle les tranches (50/25/25 si favorable) ; la MM200 seule sert à la Voie B')
    if (R.get('autofinancement') or {}).get('af') in ('NON MESURÉE', 'COMPARAISON NON DOCUMENTÉE'):
        add('Autofinancement de la croissance', 'NON', 'renseigner autofinancement.reinvestissement ; le pont de financement du §7 tranche déjà')
    if not num((R.get('profil') or {}).get('etat')):
        add('Part de l’État au capital', 'OUI, si > 50 %', 'red flag (ta règle du 28/10) ; sans effet automatique')
    if (R.get('capital') or {}).get('machine') == 'NON MESURÉE':
        add('Où va l’argent (distribution sur 3 ans)', 'NON', 'lecture de l’allocation ; capital.distribution_pct')
    R['angles_morts'] = am


def action_html(D, R):
    A_ = R.get('action') or {}
    if not A_:
        return ''
    dev = esc((D.get('meta') or {}).get('devise', ''))
    bord = 'var(--gris)' if A_['lvl'] == 'gris' else 'var(--l%s)' % (5 if A_['lvl'] == 6 else A_['lvl'])
    lignes = []
    if A_.get('ordre'):
        lignes.append('<div class="act-row"><span>%s</span><b>%s</b></div>' % (
            '⚖️ Arbitrage' if A_['ordre'].startswith('arbitrage') else '📌 Ordre', esc(A_['ordre'][:1].upper() + A_['ordre'][1:])))
    if A_.get('voie_b'):
        lignes.append('<div class="act-row"><span>🎯 Voie B</span><b>%s</b></div>' % esc(A_['voie_b']))
    if A_.get('plan_tactique'):
        lignes.append('<div class="act-row"><span>🎯 Plan enregistré</span><b>%s</b></div>' % esc(A_['plan_tactique']))
    if A_.get('rdv') or A_.get('rdv_txt'):
        lignes.append('<div class="act-row"><span>📅 Rendez-vous</span><b>%s%s</b></div>' % (
            esc(A_.get('rdv') or 'date à fixer'), (' — ' + esc(A_['rdv_txt'])) if A_.get('rdv_txt') else ''))
    if A_.get('voyants'):
        lignes.append('<div class="act-row"><span>🚨 Voyants</span><ol>%s</ol></div>' % ''.join('<li>%s</li>' % esc(v) for v in A_['voyants']))
    _pf = R.get('pf') or {}
    qui = ('Tu détiens cette ligne%s%s' % ((' (%s %% du portefeuille)' % fr(A_['pos'], 1)) if num(A_.get('pos')) else '',
                                          (' · registre du %s' % esc(_pf.get('maj'))) if _pf.get('ligne') else '')) if A_.get('detenue') else (
        'Nouvelle position' + (' · absente de ton registre du %s' % esc(_pf.get('maj')) if _pf.get('registre') else ''))
    return ('<div class="action" style="border-color:%s"><div class="act-l"><div class="lab">🧭 Que faire · %s</div>'
            '<div class="act-v" style="color:%s">%s</div><p>%s.</p></div><div class="act-r">%s</div></div>') % (
        bord, esc(qui), bord, esc(A_['act']), esc(A_['pourquoi'][:1].upper() + A_['pourquoi'][1:]) if A_.get('pourquoi') else '', ''.join(lignes))


def fait_cle_html(R):
    F = R.get('fait_cle') or {}
    if not F:
        return ''
    return ('<div class="fk"><div class="lab">🔑 Le fait qui explique le prix%s</div><p class="fk-f">%s</p>'
            '<div class="grid g2" style="gap:10px 28px">%s%s</div></div>') % (
        ' · détecté par le moteur' if F.get('auto') else '', esc(F['fait']),
        ('<div><div class="lab">Pourquoi le marché doute</div><p class="sub" style="margin-top:4px">%s</p></div>' % esc(F['doute'])) if F.get('doute') else '',
        ('<div><div class="lab">Ce qui ferait basculer l’opinion</div><p class="sub" style="margin-top:4px">%s</p></div>' % esc(F['bascule'])) if F.get('bascule') else '')


def pari_html(D, R):
    """V24 : asymetrie, esperance ponderee et confiance, en quatre cartes."""
    As, C = R.get('asymetrie') or {}, R.get('confiance') or {}
    if not As and not C:
        return ''
    cartes = []
    if As:
        p = As.get('perte')
        cartes.append(carte('Si je me suis trompé', ('%s %%' % fr(p, 0, True)) if num(p) else 'n.d.',
                            L_CAP(100 + p) if num(p) else 'gris', 'baissier à 4 ans, dividendes compris'))
        cartes.append(carte('Si j’ai raison', ('×%s' % fr(As.get('fois'), 1)) if num(As.get('fois')) else 'n.d.',
                            5 if num(As.get('fois')) and As['fois'] >= 2 else 4 if num(As.get('fois')) else 'gris',
                            'haussier : %s %%/an sur 4 ans' % fr(As.get('tri_h'), 1)))
        cartes.append(carte('Espérance pondérée', ('%s %%/an' % fr(As.get('esp'), 1)) if num(As.get('esp')) else 'n.d.',
                            L_RDT_TX(As.get('esp'), R.get('tx')) if num(As.get('esp')) else 'gris',
                            'TRI des flux pondérés 25/50/25'))
    if C:
        cartes.append(carte('Confiance', '%s %%' % fr(C['pct'], 0), C['lvl'],
                            'convention, pas une probabilité · %s' % ('calculée' if C['src'] == 'calculée' else 'déclarée')))
    det = ''
    if C and C.get('pts'):
        det = ('<details><summary>D’où vient la confiance de %s %%</summary><div class="scroll"><table>%s'
               '<tr><td><b>Base 50 + indices = %s, bornée 30–95</b></td><td class="n"><b>%s %%</b></td></tr></table></div>'
               '<p class="sub">Réponse à ta question : si j’achète au prix maximum d’achat, ce trade a-t-il un avenir sain ? Catalyseurs, '
               'signaux qui ne faiblissent pas, vents porteurs montent la note ; preuves manquantes et signaux contraires la baissent. %s</p></details>') % (
            fr(C['pct'], 0), ''.join('<tr><td>%s</td><td class="n t%s">%s</td></tr>' % (esc(l), 5 if p_ > 0 else 2, fr(p_, 0, True)) for l, p_ in C['pts']),
            fr(C['brut'], 0), fr(C['pct'], 0), ('Valeur %s.' % esc(C['src'])) if C['src'] != 'calculée' else '')
    return ('<div class="c pari"><h3 style="margin:0">⚖️ Le pari <span style="margin-left:12px;vertical-align:middle">%s</span></h3>'
            '<div class="grid g4" style="margin-top:14px">%s</div>%s</div>') % (
        bdg(As.get('lab', ''), As.get('lvl', 'gris'), 'gros wrap') if As.get('lab') else '', ''.join(cartes), det)


def voie_b_html(D, R):
    B = R.get('voie_b') or {}
    if not B or B.get('statut') in ('SANS OBJET', 'NON ÉVALUÉE', 'EN SUIVI', ''):
        return ''
    dev = esc((D.get('meta') or {}).get('devise', ''))
    rows = ''.join('<tr><td>%s</td><td>%s</td><td class="sub" style="margin:0">%s</td></tr>' % (
        esc(n), '✅' if o else '⚪' if o is None else '❌', esc(t)) for n, o, t in B.get('tests') or [])
    sortie = ''
    if B.get('statut') in ('OUVERTE', 'EN ATTENTE', 'HORS ZONE'):
        sortie = ('<div class="grid g4" style="margin-top:16px">%s%s%s%s</div>') % (
            carte('🚪 Plafond d’entrée', '%s %s' % (fprix(B.get('plafond')), dev), 4,
                  'au-dessus : potentiel < %s %% ou capital préservé < %s/100' % (fr(VOIE_B_HAUSSE_MIN, 0), fr(VOIE_B_CAP_MIN, 0))),
            carte('🎯 Objectif de sortie', '%s %s' % (fprix(B.get('vp')), dev), 5, '%s %% de potentiel · vendre quand il est atteint' % fr(B.get('hausse'), 0, True)),
            carte('⏱️ Stop temps', esc(B.get('sortie_temps') or 'n.d.'), 4, 'catalyseur passé sans revalorisation → vendre'),
            carte('🛑 Stop thèse', 'écrit' if B.get('sortie_these') else 'à écrire', 3, esc(B.get('sortie_these') or 'invalidation non écrite')))
    trig = ''
    if num(B.get('declencheur')):
        sg = B.get('au_signal') or {}
        trig = ('<p class="enclair" style="margin-top:14px">🔔 Déclencheur : le cours repasse au-dessus de <b>%s %s</b> (moyenne 200 jours). Pose une alerte, '
                'puis <b>relance le dossier</b> : tous les critères se revérifient au prix d’exécution. Au signal, avec les chiffres d’aujourd’hui : potentiel %s, '
                'capital préservé %s/100%s.</p>') % (fprix(B['declencheur']), dev, (fr(sg.get('hausse'), 0, True) + ' %') if num(sg.get('hausse')) else 'n.d.',
                                                   fr(sg.get('cap'), 0), ' → hors zone d’achat' if B.get('statut') == 'HORS ZONE' else '')
    return ('<div class="c voieb"><h3 style="margin:0">🎯 Voie B — opportunité de revalorisation (12–18 mois)</h3><div style="margin-top:10px">%s</div>'
            '<p style="margin-top:12px">%s.</p>%s<div class="scroll"><table>%s</table></div>%s'
            '<p class="sub">La Voie A répond à « puis-je la garder 3 à 5 ans sans trembler ? ». La Voie B répond à « le marché va-t-il corriger un mauvais prix '
            'dans l’année ? ». Elle exige moins de qualité, mais plus de preuves de prix, un catalyseur daté et un cours qui confirme. Taille : %s %% au plus, '
            '%s places Voie B au plus sur 20. La sortie s’écrit le jour de l’achat et ne se renégocie pas : c’est la voie des pièges à valeur si on la garde « parce que ça va remonter ». '
            'Aucun effet sur la Voie A (prix, taux exigé, taille, verdict).</p></div>') % (
        bdg(B['lab'], B['lvl'], 'gros wrap'), esc(B['txt'][:1].upper() + B['txt'][1:]), trig, rows, sortie, fr(VOIE_B_TAILLE, 0), VOIE_B_PLACES)


def angles_morts_html(R):
    am = R.get('angles_morts') or []
    if not am:
        return ''
    rows = ''.join('<tr><td>%s</td><td>%s</td><td class="sub" style="margin:0">%s</td></tr>' % (
        esc(q), bdg(c, 3 if c.startswith('OUI') else 4 if c == 'RYTHME' else 'gris'), esc(t)) for q, c, t in am)
    return ('<div class="c"><h3>🕳️ Angles morts — ce que ce dossier n’a pas pu vérifier</h3><div class="scroll"><table>'
            '<tr><th>Donnée absente</th><th>Peut changer la décision ?</th><th>Pourquoi</th></tr>%s</table></div>'
            '<p class="sub">Les blocs vides ne s’affichent plus dans le dossier : ils sont regroupés ici.</p></div>') % rows


def porte_ouverture_html(D, R):
    """V24 : quand l'achat est bloque, l'episode « Le plan » dit ce qui rouvrirait la porte."""
    P = dict(R.get('portes') or [])
    dev = esc((D.get('meta') or {}).get('devise', ''))
    Q = (R.get('q') or {}).get('Q')
    fl, fp = _pilier_faible(R)
    items = []
    if P.get('Qualité') is False:
        items.append('🏛️ <b>Qualité</b> : %s %% aujourd’hui, il faut 70 %%. Le point faible est <b>%s (%s %%)</b> — c’est lui qu’une prochaine publication doit relever.'
                     % (fr(Q, 0), esc((fl or 'n.d.').lower()), fr(fp, 0)))
    if P.get('Preuves') is False:
        items.append('🧾 <b>Preuves</b> : %s. Il faut un fait opérationnel <i>et</i> une preuve de persistance (commandes, rétention, guidance chiffrée).'
                     % esc(R.get('preuves_motif') or 'confirmations insuffisantes'))
    if P.get('Croissance') is False:
        items.append('📈 <b>Croissance</b> : %s %%/an au central, il faut 5 %%.' % fr(R.get('gc'), 1))
    if P.get('Prix') is False and num(R.get('PA')):
        items.append('💶 <b>Prix</b> : le cours doit revenir sous %s %s.' % (fprix(R['PA']), dev))
    for n in ('Guidance', 'Ancrage', 'Unités', 'Plancher −40 %'):
        if P.get(n) is False:
            items.append('🚪 <b>%s</b> : porte fermée, voir les coulisses.' % esc(n))
    if not items:
        return ''
    return ('<div class="c"><h3>🔓 Ce qui rouvrirait la porte de l’achat standard</h3><ul class="ouvre">%s</ul></div>'
            % ''.join('<li>%s</li>' % x for x in items))


CSS_V24 = """
.action{display:grid;grid-template-columns:minmax(0,1.1fr) minmax(0,1.4fr);gap:22px 34px;border:2px solid var(--gris);border-radius:16px;
padding:24px 28px;margin:0 0 20px;background:linear-gradient(135deg,rgba(57,214,224,.07),rgba(0,0,0,0) 60%)}
.act-v{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:30px;font-weight:700;line-height:1.15;margin:8px 0 12px;letter-spacing:-.01em}
.act-l p{font-size:17px;margin:0}
.act-r{display:flex;flex-direction:column;gap:12px;font-size:15.5px}
.act-row{display:grid;grid-template-columns:118px 1fr;gap:10px;align-items:baseline;border-top:1px solid var(--bord2);padding-top:10px}
.act-row:first-child{border-top:none;padding-top:0}
.act-row span{color:var(--txt2);font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:13.5px}
.act-row b{font-weight:500}
.act-row ol{margin:0;padding-left:20px}.act-row ol li{padding:0;margin:0 0 6px;font-size:15px}.act-row ol li::before{content:none}
.fk{border:1px solid #6b5a1f;border-radius:14px;padding:18px 22px;margin:0 0 18px;background:rgba(242,207,91,.06)}
.fk-f{font-size:20px;line-height:1.5;margin:8px 0 12px;color:var(--txt);max-width:none}
.pari .big{font-size:30px}
.voieb{border-color:#6b5a1f}
ul.ouvre li::before{content:none}ul.ouvre li{padding-left:0}
.lexique dt{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--cy);font-size:14px;margin-top:10px}
.lexique dd{margin:2px 0 0;color:var(--txt2);font-size:15px}
.ga-pf{display:flex;flex-wrap:wrap;gap:6px;margin-top:6px}
@media(max-width:820px){.action{grid-template-columns:1fr}.act-v{font-size:25px}.act-row{grid-template-columns:1fr;gap:2px}}
"""

LEXIQUE = [
    ('Fiabilité A / B / C / D', 'qualité des preuves, pas prévisibilité : A faits officiels rapprochés · B solides avec estimations secondaires · '
     'C incertitude matérielle bornée (+1 pt de taux, taille ×0,7) · D intrant décisif invérifiable, achat bloqué.'),
    ('P / C / E', 'provenance d’un chiffre : P publié · C calculé · E estimé (hypothèse de l’analyste).'),
    ('TRI', 'taux de rendement interne : ce que tu gagnes par an, net d’impôts et de frais, dividendes compris.'),
    ('Taux exigé', 'le rendement minimum que cette ligne doit offrir, 12 à 21 % selon les risques que les flux ne chiffrent pas.'),
    ('Prix maximum d’achat', 'le cours le plus haut auquel le TRI atteint encore le taux exigé (et qui respecte la règle des −40 %).'),
    ('Capital préservé', 'ce qui te reste sur 100 € si le scénario baissier arrive, après 4 ans, dividendes compris.'),
    ('CFO / FCF', 'flux d’exploitation (cash généré par l’activité) / flux libre (CFO moins investissements).'),
    ('BFR', 'besoin en fonds de roulement : stocks + créances clients − dettes fournisseurs. Quand il gonfle, le bénéfice ne devient pas du cash.'),
    ('Multiple hors cash', '(cours − trésorerie nette) / (BPA − produits financiers) : ce que coûte le business seul.'),
    ('ROIC', 'rentabilité du capital investi après impôt : chaque euro mis dans le business rapporte-t-il plus que son coût ?'),
    ('Voie A / Voie B', 'A : société à garder 3 à 5 ans (porte qualité 70 %). B : achat tactique de 12 à 18 mois sur une revalorisation datée, 2 % au plus.'),
]


def lexique_html():
    return '<details class="c"><summary>📖 Petit lexique du dossier</summary><dl class="lexique">%s</dl></details>' % ''.join(
        '<dt>%s</dt><dd>%s</dd>' % (esc(t), esc(d)) for t, d in LEXIQUE)



# ===================================================================== V25.0 : le recit (page 1)
# Le dossier commence par une page qui se lit comme on parle : un titre-verdict, deux paragraphes, puis quatre questions
# (bonne entreprise ? prix interessant ? combien je gagne / je perds ? que faire ?), la regle des prix et pile / face.
# Lecture seule (R3) : aucun prix, taux, taille, tranche, porte ni verdict modifie ; les phrases sont remplies avec les
# chiffres deja calcules. Deux phrases de l'analyste les rendent vivantes : lecture.marche_pense et lecture.ne_voit_pas.

RECITS = {
    'BON PRIX': ('🟢 BELLE ENTREPRISE AU BON PRIX', 'vert'),
    'TROP CHERE': ('🟡 EXCELLENTE MAIS TROP CHÈRE', 'jaune'),
    'ASYMETRIQUE': ('⚖️ OPPORTUNITÉ ASYMÉTRIQUE', 'jaune'),
    'ASYMETRIQUE A CONFIRMER': ('⚖️ OPPORTUNITÉ ASYMÉTRIQUE · À CONFIRMER', 'jaune'),
    'CORRECTE CHERE': ('🟠 CORRECTE, MAIS PAS ASSEZ BON MARCHÉ', 'orange'),
    'PREUVES': ('🟡 PROMETTEUSE, IL MANQUE DES PREUVES', 'jaune'),
    'EVITER': ('🔴 À ÉVITER', 'rouge'),
    'LIGNE CHERE': ('🟠 LIGNE DEVENUE TROP CHÈRE', 'orange'),
    'HORS PERIMETRE': ('🔴 HORS DE TON PÉRIMÈTRE', 'rouge'),
    'A CORRIGER': ('⛔ DOSSIER À CORRIGER', 'rouge'),
}

ACTIONS_HUMAINES = {
    'VENDRE': 'Vends ta ligne.',
    'VENDRE (ARBITRAGE)': 'Vends, et réinvestis dans une meilleure idée.',
    'ALLÉGER': 'Allège ta ligne.',
    'GARDER, NE PAS RENFORCER': 'Garde ta ligne, sans renforcer.',
    'GARDER SOUS SURVEILLANCE': 'Garde ta ligne, sous surveillance.',
    'GARDER — TAILLE ATTEINTE': 'Garde ta ligne : elle a déjà la bonne taille.',
    'GARDER — RÉÉVALUATION INCOMPLÈTE': 'Garde ta ligne : le dossier est incomplet.',
    'RENFORCER': 'Renforce ta ligne.',
    'ACHETER': 'Achète, par tranches.',
    'RENFORCER TACTIQUEMENT (VOIE B)': 'Renforce un peu, en tactique.',
    'SURVEILLER (VOIE B HORS ZONE)': 'Ne fais rien pour l’instant : surveille le signal.',
    'SORTIR — OBJECTIF ATTEINT': 'Vends : l’objectif tactique est atteint.',
    'SORTIR — STOP TEMPS': 'Vends : le temps imparti est écoulé.',
    'SORTIR — STOP THÈSE': 'Vends : la thèse est tombée.',
    'ACHAT TACTIQUE (VOIE B)': 'Achète une petite ligne tactique.',
    'ATTENDRE LE PRIX': 'N’achète pas encore : attends le bon prix.',
    'ATTENDRE LA CONFIRMATION': 'Attends la preuve avant d’acheter.',
    'ATTENDRE LE SIGNAL (VOIE B)': 'Attends le signal du marché avant d’acheter.',
    'DOCUMENTER AVANT D’ACHETER': 'Il manque une information clé avant de décider.',
    'NE PAS ACHETER': 'Passe ton chemin.',
    'PAS DE PLACE TACTIQUE': 'Pas de place libre : tes lignes tactiques sont toutes prises.',
    'DOSSIER À CORRIGER': 'Fais corriger les chiffres avant de décider.',
    'VÉRIFIER LE REGISTRE': 'Vérifie ton registre avant de passer un ordre tactique.',
    'VÉRIFIER LE PLAN TACTIQUE': 'Vérifie le plan tactique enregistré.',
    'GARDER — SUIVI TACTIQUE': 'Garde ta ligne et suis le plan tactique enregistré.',
    'GARDER — CHANGEMENT DE VOIE À VALIDER': 'Garde ta ligne. Valide le passage en Voie A avant de renforcer.',
}


def _phrase(t):
    """Une phrase propre : majuscule initiale, point final."""
    t = str(t or '').strip()
    if not t:
        return ''
    t = t[0].upper() + t[1:]
    return t if t[-1] in '.!?…»' else t + '.'


def _minus(t, D=None):
    """V25.1 : minuscule initiale pour enchainer une phrase, sauf nom propre ou sigle (« PAX ne… » reste « PAX »)."""
    t = str(t or '').strip()
    if not t:
        return t
    mot = re.split(r'[\s,;:’\']', t, 1)[0]
    soc = _sans_accent((D or {}).get('meta', {}).get('societe') if D else '')
    if len(mot) > 1 and (mot[1:2].isupper() or (soc and _sans_accent(mot) in soc.split())):
        return t
    return t[0].lower() + t[1:]


def _pct(x, signe=True):
    return ('%s %%' % fr(x, 0, signe)) if num(x) else 'n.d.'


def _nom_court(D):
    meta = D.get('meta') or {}
    n = str(meta.get('nom_court') or '').strip()
    if n:
        return n
    s = str(meta.get('societe') or '').strip()
    return s.split()[0] if s else 'la société'


def _valeurs_4ans(D, R):
    out = {}
    if not R.get('ctx'):
        return out
    for k in ('baissier', 'central', 'haussier'):
        sc = G(D, 'valo.scenarios.%s' % k)
        if isinstance(sc, dict) and sc.get('bpa'):
            try:
                out[k] = val_term(sc, R['ctx'])
            except Exception:  # noqa: BLE001
                pass
    return out


def calc_recit(D, R):
    meta, lec = D.get('meta') or {}, D.get('lecture') or {}
    dev = meta.get('devise', '')
    cours = vv(meta.get('cours'))
    nom = _nom_court(D)
    q = R.get('q') or {}
    Q = q.get('Q')
    As, B, A_ = R.get('asymetrie') or {}, R.get('voie_b') or {}, R.get('action') or {}
    vf = str(R.get('verdict_final') or '').upper()
    P = dict(R.get('portes') or [])
    det = R.get('detenue')
    cc, fois = R.get('cap_cours'), As.get('fois')
    seules_prix = [n for n, e in P.items() if e is False] == ['Prix']
    # -- type de situation
    if A_.get('dossier_a_corriger'):
        typ = 'A CORRIGER'  # V25.1 : des chiffres faux ne racontent pas d'histoire
    elif 'PÉRIMÈTRE' in vf or 'PERIMETRE' in vf:
        typ = 'HORS PERIMETRE'
    elif vf.startswith(('ACHAT', 'RENFORCEMENT')) and not A_.get('plan_tactique') and not A_.get('act', '').startswith(('VENDRE', 'ALLÉGER', 'SORTIR')):
        typ = 'BON PRIX'
    elif det and A_.get('act', '').startswith(('VENDRE', 'ALLÉGER')):
        typ = 'LIGNE CHERE' if not ('REJET' in vf or (num(Q) and Q < 55)) else 'EVITER'
    elif 'REJET' in vf or (num(Q) and Q < 55):
        typ = 'EVITER'
    elif num(cc) and cc < CAP_MIN and num(Q) and Q >= 70 and not det:
        typ = 'TROP CHERE' if Q >= 75 else 'CORRECTE CHERE'  # belle entreprise, mais le prix expose trop a la baisse
    elif num(cc) and cc < CAP_MIN:
        typ = 'EVITER'
    elif num(cc) and cc >= 80 and num(fois) and fois >= 2:
        typ = 'ASYMETRIQUE' if (B.get('statut') == 'OUVERTE' or vf.startswith(('ACHAT', 'RENFORCEMENT'))) else 'ASYMETRIQUE A CONFIRMER'
    elif seules_prix and num(Q) and Q >= 75:
        typ = 'TROP CHERE'
    elif P.get('Prix') is False:
        typ = 'CORRECTE CHERE'
    elif vf.startswith(('ACHAT', 'RENFORCEMENT')) and not A_.get('plan_tactique'):
        typ = 'BON PRIX'
    else:
        typ = 'PREUVES'
    etiq, coul = RECITS[typ]
    # -- titre
    F = R.get('fait_cle') or {}
    if str(lec.get('titre') or '').strip():
        titre = _phrase(lec['titre'])
    elif R.get('ve_negative') and R.get('ve_verif') and typ in ('ASYMETRIQUE', 'ASYMETRIQUE A CONFIRMER', 'BON PRIX', 'PREUVES'):
        titre = 'Le marché te vend %s moins cher que l’argent qu’elle a en caisse.' % nom
    else:
        titre = {'BON PRIX': 'Belle entreprise, et enfin à un bon prix.',
                 'TROP CHERE': 'Excellente entreprise, mais encore trop chère.',
                 'ASYMETRIQUE': ('Pile tu gagnes beaucoup, face tu perds peu.' if (num(cc) and cc >= 90)
                                 else 'Beaucoup à gagner, pour une perte limitée.'),
                 'ASYMETRIQUE A CONFIRMER': ('Pile tu gagnes beaucoup, face tu perds peu : reste à le confirmer.' if (num(cc) and cc >= 90)
                                             else 'Beaucoup à gagner, pour une perte limitée : reste à le confirmer.'),
                 'CORRECTE CHERE': 'Correcte, mais pas assez bon marché pour le risque.',
                 'PREUVES': 'Prometteuse, mais il manque encore des preuves.',
                 'EVITER': ('Pas chère, mais pour de bonnes raisons.' if (num(R.get('retenu')) and num(R.get('tx')) and R['retenu'] >= R['tx'])
                            else 'Trop fragile pour mériter une de tes vingt places.'),
                 'LIGNE CHERE': ('Toujours une belle entreprise, mais elle ne rapporte plus assez à ce prix.' if (num(Q) and Q >= 70)
                                 else 'Elle ne rapporte plus assez à ce prix.'),
                 'HORS PERIMETRE': 'Hors de ton périmètre d’investissement.',
                 'A CORRIGER': 'Les chiffres de ce dossier doivent être corrigés avant toute décision.'}[typ]
    # -- chapeau
    chap = []
    tnm, cap = vv(G(D, 'plancher.tresorerie_nette_meur')), vv(meta.get('capitalisation_meur'))
    tna = vv(G(D, 'valo.tresorerie_nette_action'))
    if R.get('ve_negative') and R.get('ve_verif') and num(tna) and num(cours) and typ != 'LIGNE CHERE':
        chap.append('Par action, %s détient <b class="chiffre">%s %s</b> de trésorerie nette comptable, pour un cours de <b class="chiffre">%s %s</b>%s.'
                    % (esc(nom), fprix(tna), esc(dev), fprix(cours), esc(dev),
                       (' : toute la société vaut %s M€ en bourse, pour %s M€ de cash net' % (fr(cap, 0), fr(tnm, 0))) if (num(cap) and num(tnm)) else ''))
    elif R.get('ve_negative') and num(tnm) and num(cap) and typ != 'LIGNE CHERE':
        chap.append('Selon la capitalisation déclarée, %s détient <b class="chiffre">%s M€</b> de trésorerie nette pour <b class="chiffre">%s M€</b> en bourse (à recouper avec le cash par action).'
                    % (esc(nom), fr(tnm, 0), fr(cap, 0)))
    elif F.get('fait') and not F.get('auto'):
        chap.append(esc(_phrase(F['fait'])))
    mp = str(lec.get('marche_pense') or '').strip()
    nv = str(lec.get('ne_voit_pas') or '').strip()
    if mp:
        chap.append(esc(_phrase(('Le marché semble penser que ' + _minus(mp, D)) if not mp.lower().startswith(('le marché', 'les investisseurs', 'il ')) else mp)))
    elif F.get('doute'):
        chap.append(esc(_phrase(F['doute'])))
    if not mp:
        warn('V25 : lecture.marche_pense absent — la page 1 reprend le point décisif. Écrire une inquiétude du marché, sans lui prêter de certitude.')
    if not nv:
        warn('V25 : lecture.ne_voit_pas absent — écrire ce que le prix ne voit pas, avec le test observable qui le confirmera.')
    suite = []
    if nv:
        cible = B.get('vp') if num(B.get('vp')) else None
        p_ = esc(_phrase(('Mais le prix ne tient pas compte de ' + _minus(nv, D)) if not nv.lower().startswith(('mais', 'le prix', 'ce que')) else nv))
        if cible and num(cours) and B.get('statut') in ('OUVERTE', 'EN ATTENTE', 'HORS ZONE') and cible > cours:
            p_ = p_ + ' Si c’est le cas, le cours peut remonter vers <b class="chiffre">%s %s</b> en un ou deux ans (%s).' % (
                fprix(cible), esc(dev), _pct(100 * (cible / cours - 1)))
        suite.append(p_)
    bascule = str(F.get('bascule') or '').strip() if F else ''
    cond0 = str(G(D, 'verdict.suivi_condition') or '').strip()
    rdv0 = _date((R.get('action') or {}).get('rdv'))
    MOIS = ['janvier', 'février', 'mars', 'avril', 'mai', 'juin', 'juillet', 'août', 'septembre', 'octobre', 'novembre', 'décembre']
    if typ.startswith('ASYMETRIQUE') and (bascule or rdv0):
        if bascule and not (cond0 and bascule[:40] == cond0[:40]):
            suite.append('Ce qui ferait basculer l’opinion : %s C’est tout le pari.' % esc(_phrase(bascule)[0].lower() + _phrase(bascule)[1:]))
        elif rdv0:
            suite.append('La réponse tombera avec les comptes du %s %s %s. C’est tout le pari.' % (
                rdv0.day if rdv0.day > 1 else '1er', MOIS[rdv0.month - 1], rdv0.year))
    # -- question 1 : bonne entreprise ?
    q1 = ('Exceptionnelle.' if Q >= 85 else 'Très bonne.' if Q >= 75 else 'Bonne.' if Q >= 70 else 'Correcte, sans plus.' if Q >= 60
          else 'Fragile.') if num(Q) else 'Pas encore évaluée.'
    q1c = 'vert' if (num(Q) and Q >= 70) else 'orange' if (num(Q) and Q >= 60) else 'rouge' if num(Q) else 'gris'
    t1 = []
    if num(Q) and (q.get('provisoire') or (num(q.get('cov')) and q['cov'] < 80)):  # V25.1 : pas d'« Exceptionnelle » sur 5 % des controles
        q1, q1c = 'Impossible à dire pour l’instant.', 'gris'
        t1.append('La note de %s %% ne repose que sur %s %% des contrôles : elle est provisoire.' % (fr(Q, 0), fr(q.get('cov'), 0)))
    act0 = _premiere_phrase(G(D, 'acte0.activite'), 240)
    if act0:
        t1.append(esc(act0))
    pil = [(p.get('pct'), p.get('lab')) for p in (q.get('pil') or {}).values() if num(p.get('pct'))]
    if pil:
        fort, faible = max(pil, key=lambda t: t[0]), min(pil, key=lambda t: t[0])
        t1.append('Son point fort : %s (%s %%). Son point faible : %s (%s %%).' % (
            esc(fort[1].lower()), fr(fort[0], 0), esc(faible[1].lower()), fr(faible[0], 0)))
    rb = R.get('rentab') or {}
    if rb.get('tend') == 'EN BAISSE' and rb.get('vals'):
        t1.append('Sa rentabilité du capital baisse depuis %s (de %s %% à %s %%).' % (rb['annees'][0], fr(rb['vals'][0], 0), fr(rb['vals'][-1], 0)))
    elif rb.get('tend') == 'EN HAUSSE' and rb.get('vals'):
        t1.append('Sa rentabilité du capital progresse depuis %s (de %s %% à %s %%).' % (rb['annees'][0], fr(rb['vals'][0], 0), fr(rb['vals'][-1], 0)))
    av = R.get('avenir') or {}
    if av.get('txt'):
        t1.append(esc(_phrase(av['txt'])))
    if q1c != 'gris':
        t1.append({True: 'Une entreprise que tu peux garder des années.', False: 'Ce n’est pas une entreprise à garder dix ans les yeux fermés.'}[bool(num(Q) and Q >= 70)])
    # -- question 2 : prix ?
    rt, tx, PA = R.get('retenu'), R.get('tx'), R.get('PA')  # PA est deja plafonne par la regle des -40 % (appliquer_plancher)
    if not R.get('calc'):
        q2, q2c, t2 = 'Pas encore calculé.', 'gris', ['La valorisation n’a pas pu être faite : il manque des chiffres clés.']
    else:
        pp = R.get('porte_prix')
        if pp == 'ouverte':
            q2, q2c = ('Oui, très.', 'vert') if (num(rt) and num(tx) and rt >= tx + 5) else ('Oui.', 'vert')
        elif pp == 'PROCHE':
            q2, q2c = 'Presque.', 'jaune'
        else:
            q2, q2c = 'Non, pas encore.', 'rouge'
        if pp == 'ouverte' and typ in ('TROP CHERE', 'CORRECTE CHERE'):
            q2, q2c = 'Le rendement oui, le risque non.', 'orange'
        t2 = ['Au cours du jour, le dossier attend <b class="chiffre %s">%s</b> %% par an, alors que ton seuil pour ce niveau de risque est de %s %%.'
              % (q2c, fr(rt, 0), fr(tx, 0))]
        if typ == 'EVITER':
            t2.append('Mais un prix bas ne suffit pas : c’est l’entreprise elle-même qui pose problème.' if pp == 'ouverte' else
                      'Et même plus bas, l’entreprise resterait trop fragile pour toi.')
        elif (pp != 'ouverte' or typ in ('TROP CHERE', 'CORRECTE CHERE')) and num(PA) and num(cours) and cours > 0 and PA < cours:
            t2.append('Le multiple est trop haut aujourd’hui : crée une alerte à <b class="chiffre cyan">%s %s</b> (%s par rapport au cours actuel). À ce prix-là, le rendement atteint ton seuil sans trop t’exposer à la baisse.'
                      % (fprix(PA), esc(dev), _pct(100 * (PA / cours - 1))))
    # -- question 3 : gagner / perdre
    perte = As.get('perte')
    lab_as = As.get('lab', '')
    q3 = {'PILE JE GAGNE, FACE JE PERDS PEU': 'Beaucoup, contre presque rien.', 'ASYMÉTRIE FAVORABLE': 'Bien plus que ce que tu risques.',
          'ASYMÉTRIE CORRECTE': 'Un peu plus que ce que tu risques.', 'PARI SYMÉTRIQUE': 'Autant que ce que tu risques.'}.get(lab_as, 'Pas encore mesuré.')
    q3c = {'PILE JE GAGNE, FACE JE PERDS PEU': 'vert', 'ASYMÉTRIE FAVORABLE': 'vert', 'ASYMÉTRIE CORRECTE': 'jaune', 'PARI SYMÉTRIQUE': 'orange'}.get(lab_as, 'gris')
    V4 = _valeurs_4ans(D, R)
    if num(B.get('vp')) and B.get('statut') in ('OUVERTE', 'EN ATTENTE', 'HORS ZONE') and num(cours) and B['vp'] > cours:
        pile_v = _pct(100 * (B['vp'] / cours - 1))
        pile_t = 'vers l’objectif tactique de %s %s, à l’échéance du %s.' % (fprix(B['vp']), esc(dev), esc(B.get('sortie_temps') or 'n.d.'))
        q3, q3c = 'Deux horizons à lire séparément.', 'jaune'
    elif num(fois):
        pile_v = _pct(100 * (fois - 1))
        pile_t = 'en quatre ans si tout va bien (%s %% par an, dividendes compris)%s.' % (fr(As.get('tri_h'), 0), (', vers %s %s' % (fprix(V4['haussier']), esc(dev))) if num(V4.get('haussier')) else '')
    else:
        pile_v, pile_t = 'n.d.', 'scénario favorable non chiffré.'
    if num(perte):
        face_v = _pct(min(perte, 0)) if perte < 0 else '0 %'
        face_t = ('en quatre ans, dividendes compris, si le scénario défavorable arrive.' +
                  (' La trésorerie amortit la chute.' if (R.get('ve_negative') and perte > -15) else '') if perte < 0 else
                  'même le scénario défavorable rend ta mise en quatre ans, dividendes compris.')
        face_t += ' Ce n’est pas une perte maximale.'
    else:
        face_v, face_t = 'n.d.', 'scénario défavorable non chiffré.'
    # V25.1 : si l'entree se fait a un autre prix (alerte), montrer le meme pari a ce prix-la
    entree, ent_lib = None, ''
    if B.get('statut') in ('EN ATTENTE', 'HORS ZONE') and num(B.get('declencheur')) and not str(A_.get('act', '')).startswith(('VENDRE', 'ALLÉGER', 'SORTIR')):
        entree, ent_lib = B['declencheur'], 'au prix du signal'
    elif not det and num(PA) and num(cours) and PA < cours and str(A_.get('act', '')) in ('ATTENDRE LE PRIX', 'NE PAS ACHETER') \
            and typ in ('TROP CHERE', 'CORRECTE CHERE'):
        entree, ent_lib = PA, 'au prix de ton alerte'
    q3_apres = ''
    if num(entree) and num(cours) and abs(entree / cours - 1) > 0.01:
        cap_e = cap_au_prix(R, entree)
        if num(B.get('vp')) and B.get('statut') in ('EN ATTENTE', 'HORS ZONE'):
            pile_e = 100 * (B['vp'] / entree - 1)
        elif num(V4.get('haussier')):
            pile_e = 100 * (V4['haussier'] / entree - 1)
        else:
            pile_e = None
        horiz = 'l’objectif tactique' if ent_lib == 'au prix du signal' else 'le cours haussier à quatre ans'
        q3_apres = ('%s (<b class="chiffre cyan">%s %s</b>), potentiel vers %s <b class="chiffre vert">%s</b> et '
                    'baissier à quatre ans, dividendes compris, <b class="chiffre rouge">%s</b>.' % (
                        ent_lib.capitalize(), fprix(entree), esc(dev), horiz, _pct(pile_e), _pct(cap_e - 100 if num(cap_e) else None)))
    t3 = []
    if num(As.get('esp')):
        t3.append('En pondérant les trois scénarios, tu peux espérer environ <b class="chiffre">%s</b> %% par an. Score de confiance : %s %%.'
                  % (fr(As['esp'], 0), fr((R.get('confiance') or {}).get('pct'), 0)))
    if typ == 'A CORRIGER':
        q2, q2c, t2 = 'À vérifier.', 'gris', ['Les prix de ce dossier doivent être vérifiés.']
        q3, q3c, t3 = 'À vérifier.', 'gris', []
        pile_v, pile_t = 'n.d.', 'Scénario favorable à recalculer.'
        face_v, face_t = 'n.d.', 'Scénario défavorable à recalculer.'
        q3_apres = ''
    # -- question 4 : que faire -- V25.1 : la page 1 TRADUIT l'action du moteur, elle n'en invente aucune
    act = A_.get('act', '')
    pq = str(A_.get('pourquoi') or '')
    titre_act = ACTIONS_HUMAINES.get(act, _phrase(act.lower()))
    pos_ = vv(meta.get('position_pct'))
    tl = R.get('taille') or {}
    plaf = B.get('plafond')
    inv = _premiere_phrase(G(D, 'lecture.invalidation'), 240)
    taille_b_ok = not (det and num(pos_) and pos_ >= VOIE_B_TAILLE)
    if typ in ('TROP CHERE', 'CORRECTE CHERE') and not det and act in ('NE PAS ACHETER', 'ATTENDRE LE PRIX'):
        titre_act = 'N’achète pas encore : attends le bon prix.'
    if act == 'GARDER, NE PAS RENFORCER':
        if B.get('statut') == 'EN ATTENTE' and taille_b_ok:
            titre_act = 'Garde ta ligne, et attends le signal pour renforcer.'
        elif B.get('statut') == 'HORS ZONE':
            titre_act = 'Garde ta ligne, sans renforcer pour l’instant.'
        elif B.get('statut') in ('OUVERTE', 'EN ATTENTE') and not taille_b_ok:
            titre_act = 'Garde ta ligne : elle a déjà sa taille tactique.'
        elif B.get('statut') == 'OUVERTE' and not num(pos_):
            titre_act = 'Garde ta ligne : indique son poids avant de renforcer.'
    elif act == 'RENFORCER TACTIQUEMENT (VOIE B)':
        titre_act = 'Porte ta ligne à %s %%, en renfort tactique.' % fr(VOIE_B_TAILLE, 0)
    elif act == 'ACHAT TACTIQUE (VOIE B)':
        titre_act = 'Prends une petite ligne tactique de %s %%.' % fr(VOIE_B_TAILLE, 0)
    D_ = lambda x: '<b class="chiffre cyan">%s %s</b>' % (fprix(x), esc(dev))
    etapes = []
    engage = det or act in ('ACHETER', 'RENFORCER', 'ACHAT TACTIQUE (VOIE B)', 'RENFORCER TACTIQUEMENT (VOIE B)')
    tactique = act in ('ACHAT TACTIQUE (VOIE B)', 'RENFORCER TACTIQUEMENT (VOIE B)')
    if act.startswith('SORTIR'):
        etapes.append('Vends la ligne tactique : %s. C’était la sortie écrite le jour de l’achat, elle ne se discute pas.' % esc(pq))
    elif act == 'DOSSIER À CORRIGER':
        etapes.append('Vérifie les données signalées (%s), puis relance le dossier.' % esc(pq))
    elif A_.get('plan_tactique') and not act.startswith('VENDRE'):
        etapes.append('Plan enregistré à l’achat : %s.' % esc(A_['plan_tactique'].rstrip('.')))
    elif act == 'VÉRIFIER LE REGISTRE':
        etapes.append(esc(_phrase(pq)))
    elif act.startswith('VENDRE'):
        etapes.append('Vends la ligne : %s.' % esc(pq))
        etapes.append(('Garde le dossier sous le coude : sous %s, il redevient intéressant.' % D_(PA)) if num(PA)
                      else 'Garde le dossier sous le coude, au cas où le prix retomberait.')
    elif act == 'ALLÉGER':
        etapes.append('Allège la ligne : %s.' % esc(pq))
    elif act == 'ACHETER':
        etapes.append('Achète la première tranche (répartition %s), au plus à %s. Taille maximale de la ligne : %s %% du portefeuille.'
                      % (esc(R.get('tranches') or 'n.d.'), D_(PA), fr(tl.get('max'), 1)))
    elif act == 'RENFORCER':
        etapes.append('Renforce jusqu’à %s %% du portefeuille%s, au plus à %s.'
                      % (fr(tl.get('max'), 1), (' (aujourd’hui %s %%)' % fr(pos_, 1)) if num(pos_) else '', D_(PA)))
    elif tactique:
        etapes.append('%s, sans payer plus de %s : au-dessus, le potentiel ou la protection ne tiennent plus.'
                      % (('Porte la ligne de %s %% à %s %% au plus' % (fr(pos_, 1), fr(VOIE_B_TAILLE, 0))) if det
                         else 'Prends une ligne de %s %% au plus' % fr(VOIE_B_TAILLE, 0), D_(plaf)))
        etapes.append('Ta sortie, écrite dès aujourd’hui : vends à <b class="chiffre vert">%s %s</b> (objectif), au plus tard le <b>%s</b> (stop temps), '
                      'ou tout de suite si %s (stop thèse).' % (fprix(B.get('vp')), esc(dev), esc(B.get('sortie_temps') or 'n.d.'),
                                                                esc(_minus(inv, D)) if inv else 'la thèse tombe'))
    elif B.get('statut') == 'EN ATTENTE' and num(B.get('declencheur')) and num(cours) and taille_b_ok:
        etapes.append('Pose une alerte à %s (%s). S’il y remonte, relance le dossier : %s n’est permis que si tout tient encore à ce prix '
                      '(plafond d’entrée aujourd’hui %s).' % (D_(B['declencheur']), _pct(100 * (B['declencheur'] / cours - 1)),
                                                            'le renfort à %s %%' % fr(VOIE_B_TAILLE, 0) if det else 'l’achat tactique', D_(plaf)))
    elif B.get('statut') == 'HORS ZONE' and num(B.get('declencheur')) and num(cours):
        sg = B.get('au_signal') or {}
        etapes.append('Pose une alerte à %s, mais pour relancer l’analyse, pas pour %s. Avec les chiffres d’aujourd’hui, à ce prix le potentiel tomberait à '
                      '<b class="chiffre">%s</b> et le capital préservé à <b class="chiffre">%s</b>/100 : la Voie B se fermerait. Elle ne tient que sous %s.'
                      % (D_(B['declencheur']), 'renforcer' if det else 'acheter', _pct(sg.get('hausse')), fr(sg.get('cap'), 0), D_(plaf)))
    elif not det and num(PA) and num(cours) and PA < cours and (act == 'ATTENDRE LE PRIX' or typ in ('TROP CHERE', 'CORRECTE CHERE')):
        etapes.append('Crée une alerte à %s (%s par rapport au cours actuel). Quand elle sonne, relance le dossier avant d’acheter.'
                      % (D_(PA), _pct(100 * (PA / cours - 1))))
    elif act == 'PAS DE PLACE TACTIQUE':
        etapes.append('Tes %s places sont prises. Attends qu’une place se libère, puis relance ce dossier.' % VOIE_B_PLACES)
    elif typ == 'A CORRIGER':
        etapes.append('Ne décide rien sur ce dossier : fais corriger les chiffres (unités, ancrage) puis relance-le.')
    elif not det and (act == 'NE PAS ACHETER' or typ in ('EVITER', 'HORS PERIMETRE')):
        etapes.append('Rien à faire. Ne la remets sur ta liste que si les comptes changent vraiment l’histoire.')
    if B.get('statut') in ('EN ATTENTE', 'HORS ZONE') and not B.get('places_verifiees') and etapes and not act.startswith(('VENDRE', 'ALLÉGER', 'SORTIR')):
        etapes[0] += ' Vérifie le registre avant tout ordre tactique.'
    rdv = A_.get('rdv')
    cond = _premiere_phrase(G(D, 'verdict.suivi_condition'), 240)
    if rdv and not act.startswith(('VENDRE', 'SORTIR')) and not (not det and (act == 'NE PAS ACHETER' or typ == 'EVITER')):
        dd = _date(rdv)
        rdv_txt = ('%s %s %s' % (dd.day if dd.day > 1 else '1er', MOIS[dd.month - 1], dd.year)) if dd else rdv
        etapes.append('%s le <b>%s</b>%s' % ('Rendez-vous' if engage else 'Prochain point', esc(rdv_txt),
                                            (' : ' + esc(_minus(cond, D))) if cond else '.'))
    if engage and not tactique and not A_.get('plan_tactique') and act != 'DOSSIER À CORRIGER' and not act.startswith(('VENDRE', 'SORTIR')):
        if inv:
            etapes.append('Tu sors si la thèse tombe : %s' % esc(_minus(inv, D)))
        else:
            warn('Argent engagé sans stop thèse : écrire lecture.invalidation (seuils chiffrés qui feraient sortir).')
    etapes = etapes[:1] if typ == 'A CORRIGER' else etapes[:3]
    R['recit'] = dict(type=typ, etiquette=etiq, couleur=coul, titre=titre, chapeau=chap, suite=suite,
                      q1=(q1, q1c, t1), q2=(q2, q2c, t2), q3=(q3, q3c, t3), pile=(pile_v, pile_t), face=(face_v, face_t),
                      action=titre_act, etapes=etapes, v4=V4, q3_apres=q3_apres)


def regle_html(D, R):
    """La regle des prix : du pire au meilleur cas, sur une echelle logarithmique resserree."""
    meta = D.get('meta') or {}
    cours = vv(meta.get('cours'))
    if not (R.get('calc') and num(cours)) or (R.get('action') or {}).get('dossier_a_corriger'):
        return ''
    V4 = (R.get('recit') or {}).get('v4') or {}
    B = R.get('voie_b') or {}
    pts = []
    if num(V4.get('baissier')):
        pts.append((V4['baissier'], 'rouge', 'si je me trompe<br>dans 4 ans'))
    pts.append((cours, 'cyan', 'aujourd’hui'))
    PA = R.get('PA')
    if (R.get('porte_prix') != 'ouverte' or (R.get('recit') or {}).get('type') in ('TROP CHERE', 'CORRECTE CHERE')) and num(PA) and PA < cours:
        pts.append((PA, 'jaune', '🔔 alerte Voie A<br>prix max. d’achat'))
    elif B.get('statut') == 'EN ATTENTE' and num(B.get('declencheur')):
        pts.append((B['declencheur'], 'jaune', '🔔 alerte Voie B<br>signal → relancer'))
    elif B.get('statut') == 'HORS ZONE' and num(B.get('declencheur')):
        pts.append((B['declencheur'], 'jaune', '🔔 alerte<br>relancer l’analyse'))
    if num(B.get('plafond')) and B.get('statut') in ('OUVERTE', 'EN ATTENTE', 'HORS ZONE') and not any(abs(p[0] - B['plafond']) < 1e-9 for p in pts):
        pts.append((B['plafond'], 'orange', 'plafond d’entrée<br>tactique'))
    if num(B.get('vp')) and B.get('statut') in ('OUVERTE', 'EN ATTENTE', 'HORS ZONE'):
        pts.append((B['vp'], 'vert', 'objectif à 1 ou 2 ans'))
    if num(V4.get('central')):
        pts.append((V4['central'], 'vert', 'scénario central<br>dans 4 ans'))
    if num(V4.get('haussier')):
        pts.append((V4['haussier'], 'vert', 'si tout va bien<br>dans 4 ans'))
    pts = [p for p in pts if p[0] > 0]
    if len(pts) < 3:
        return ''
    pts.sort(key=lambda p: p[0])
    lo, hi = math.log(pts[0][0]), math.log(pts[-1][0])
    span = (hi - lo) or 1.0
    pos = [4 + 92 * (math.log(v) - lo) / span for v, _, _ in pts]
    gap = min(16.0, 92.0 / max(1, len(pts) - 1))
    for i in range(1, len(pos)):  # ecart minimal pour la lisibilite
        pos[i] = max(pos[i], pos[i - 1] + gap)
    if pos[-1] > 96:
        sh = pos[-1] - 96
        pos = [max(4.0, p - sh * (i / (len(pos) - 1))) for i, p in enumerate(pos)]
        for i in range(1, len(pos)):
            pos[i] = max(pos[i], pos[i - 1] + gap * 0.8)
    pc = pos[[p[0] for p in pts].index(cours)]
    rail = ('linear-gradient(90deg,rgba(240,96,95,.8) 0%%,rgba(240,96,95,.8) %.1f%%,#2a3a40 %.1f%%,#2a3a40 %.1f%%,rgba(78,222,154,.45) %.1f%%,rgba(78,222,154,.95) 100%%)'
            % (max(2.0, pos[0] + 2), max(2.0, pos[0] + 2), pc, pc))
    o = ['<div class="p1-regle"><div class="p1-axe" style="background:%s"></div>' % rail]
    for i, ((v, c, t), x) in enumerate(zip(pts, pos)):
        haut = (i % 2 == 1)
        o.append('<div class="p1-pt %s" style="left:%.1f%%"><div class="p1-dot" style="background:var(--p1-%s)"></div>'
                 '<div class="p1-lbl"><div class="p1-px p1-%s">%s</div><div class="p1-t">%s</div></div></div>' % (
                     'haut' if haut else 'bas', x, c, c, fprix(v), t))
    o.append('</div><div class="p1-echelle">Échelle resserrée pour la lisibilité · valeurs en %s · « dans 4 ans » = valeur estimée de l’action, hors dividendes.</div>'
             % esc(meta.get('devise', '')))
    return ''.join(o)


def _nbsp_pct(h):
    """Espace insecable avant %, : et ? pour eviter les orphelins en fin de ligne."""
    h = h.replace(' %', '\u00a0%').replace(' ?', '\u00a0?').replace(' :', '\u00a0:')
    return re.sub(r'(\(?[+\-−]?\d[\d,.]*)\u00a0%(\)?)', '<span class="nw">\\1\u00a0%\\2</span>', h)


def page1_html(D, R):
    """V25 : la page 1, fusion des maquettes A (editorial), B (regle des prix) et C (quatre questions)."""
    Rc = R.get('recit') or {}
    if not Rc:
        return ''
    meta = D.get('meta') or {}
    pf = R.get('pf') or {}
    pos = vv(meta.get('position_pct'))
    det_txt = ('tu détiens %s de ton portefeuille' % (('%s %%' % fr(pos, 1)) if num(pos) else 'cette ligne')) if R.get('detenue') else 'nouvelle position'

    def question(n, intitule, rep, t, extra=''):
        r, c, txts = rep
        return ('<section class="p1-q"><div class="p1-n">%s · %s</div><div class="p1-r p1-%s">%s</div>%s%s</section>' % (
            n, intitule, c, esc(r), ''.join('<p>%s</p>' % x for x in ([' '.join(txts)] if txts else [])), extra))
    duo = ('<div class="p1-duo"><div class="p1-pf p1-pile"><div class="p1-l">PILE · SI J’AI RAISON</div><div class="p1-v">%s</div><p>%s</p></div>'
           '<div class="p1-pf p1-face"><div class="p1-l">FACE · SI JE ME TROMPE</div><div class="p1-v">%s</div><p>%s</p></div></div>') % (
        Rc['pile'][0], Rc['pile'][1], Rc['face'][0], Rc['face'][1]) + (
        ('<p class="p1-entree">%s</p>' % Rc['q3_apres']) if Rc.get('q3_apres') else '')
    etapes = ''.join('<div class="p1-etape"><div class="p1-num">%s</div><p>%s</p></div>' % (i + 1, e) for i, e in enumerate(Rc['etapes']))
    return _nbsp_pct(('<div class="p1"><div class="p1-nom">%s</div><div class="p1-meta">%s · %s · %s · %s</div><div class="p1-cours">%s %s</div>'
            '<span class="p1-etiq p1-e-%s">%s</span><h1 class="p1-titre">%s</h1>%s%s'
            '%s%s%s%s'
            '<p class="p1-fin">↓ Le tableau de bord, puis le dossier détaillé : l’histoire, la croissance, la forteresse, les risques, le prix et le plan.</p></div>') % (
        esc(meta.get('societe')), esc(meta.get('secteur')), esc(meta.get('pays')), esc(R.get('ticker') or meta.get('ticker')), esc(det_txt),
        fprix(vv(meta.get('cours'))), esc(meta.get('devise', '')),
        Rc['couleur'], esc(Rc['etiquette']), esc(Rc['titre']),
        ('<p class="p1-chapeau">%s</p>' % ' '.join(Rc['chapeau'])) if Rc['chapeau'] else '',
        ''.join('<p>%s</p>' % s_ for s_ in Rc['suite']),
        question(1, 'EST-CE UNE BONNE ENTREPRISE ?', Rc['q1'], None),
        question(2, 'EST-CE QUE LE PRIX EST INTÉRESSANT ?', Rc['q2'], None, regle_html(D, R)),
        question(3, 'COMBIEN JE PEUX GAGNER, COMBIEN JE PEUX PERDRE ?', Rc['q3'], None, duo),
        '<section class="p1-q"><div class="p1-n">4 · QU’EST-CE QUE JE FAIS ?</div><div class="p1-action"><div class="p1-av">%s</div>%s</div></section>' % (
            esc(Rc['action']), etapes)))


CSS_V25 = """
:root{--p1-vert:#4ede9a;--p1-jaune:#f2cf5b;--p1-orange:#f0994a;--p1-rouge:#f0605f;--p1-cyan:#39d6e0;--p1-gris:#7e979d}
body{font-size:20px;text-align:center}
.wrap{max-width:1180px}
p{margin-left:auto;margin-right:auto}
.sub{margin-left:auto;margin-right:auto}
.c{padding:30px 34px}
.c h3{font-size:22px}
th,td{text-align:left}td.n,th.n{text-align:right}
ul{display:inline-block;text-align:left}
.grid>ul{display:block}
.p0{font-family:ui-monospace,monospace;font-size:13px;color:var(--gris);margin:14px auto 10px;letter-spacing:.04em;max-width:900px}
.feux{justify-content:center}
.ep h2{font-size:34px}.ep-c{margin:0 auto}
.p1{max-width:900px;margin:10px auto 40px;padding:60px 48px 54px;border:1px solid var(--bord);border-radius:28px;background:rgba(5,9,11,.93);line-height:1.75;font-size:21px}
.p1 p{max-width:36em;margin:0 auto 20px}
.p1-nom{font-size:44px;font-weight:600;line-height:1.15;letter-spacing:-.01em}
.p1-meta{color:var(--gris);font-size:16px;margin-top:8px}
.p1-cours{font-family:ui-monospace,monospace;color:var(--cy);font-size:32px;margin:8px 0 34px}
.p1-etiq{display:inline-block;font-family:ui-monospace,monospace;font-size:15px;letter-spacing:.12em;padding:9px 20px;border-radius:999px;font-weight:700}
.p1-e-jaune{background:rgba(242,207,91,.14);color:var(--p1-jaune);border:1px solid rgba(242,207,91,.45)}
.p1-e-vert{background:rgba(78,222,154,.12);color:var(--p1-vert);border:1px solid rgba(78,222,154,.45)}
.p1-e-orange{background:rgba(240,153,74,.12);color:var(--p1-orange);border:1px solid rgba(240,153,74,.45)}
.p1-e-rouge{background:rgba(240,96,95,.12);color:var(--p1-rouge);border:1px solid rgba(240,96,95,.45)}
.p1-titre{font-size:40px;line-height:1.25;margin:24px auto;max-width:17em;font-weight:600;letter-spacing:-.01em;font-family:inherit}
.p1-chapeau{font-size:23px}
.nw{white-space:nowrap}
.chiffre{font-family:ui-monospace,monospace;font-weight:700;white-space:nowrap}
.chiffre.vert,.p1-vert{color:var(--p1-vert)}.chiffre.jaune,.p1-jaune{color:var(--p1-jaune)}.chiffre.rouge,.p1-rouge{color:var(--p1-rouge)}
.chiffre.cyan,.p1-cyan{color:var(--p1-cyan)}.p1-orange{color:var(--p1-orange)}.p1-gris{color:var(--p1-gris)}
.p1-q{margin-top:64px;padding-top:42px;border-top:1px solid var(--bord)}
.p1-n{font-family:ui-monospace,monospace;font-size:16px;letter-spacing:.12em;color:var(--txt2)}
.p1-r{font-size:32px;font-weight:600;margin:8px 0 16px}
.p1-duo{display:grid;grid-template-columns:1fr 1fr;gap:22px;margin:28px 0 6px}
.p1-pf{border-radius:20px;padding:28px 26px 24px}
.p1-l{font-family:ui-monospace,monospace;letter-spacing:.2em;font-size:14px}
.p1-v{font-family:ui-monospace,monospace;font-size:56px;font-weight:700;line-height:1.1;margin:10px 0}
.p1-pf p{font-size:18px;color:var(--txt2);margin:0}
.p1-pile{background:rgba(78,222,154,.07);border:1px solid rgba(78,222,154,.4)}.p1-pile .p1-l,.p1-pile .p1-v{color:var(--p1-vert)}
.p1-face{background:rgba(240,96,95,.06);border:1px solid rgba(240,96,95,.35)}.p1-face .p1-l,.p1-face .p1-v{color:var(--p1-rouge)}
.p1-regle{position:relative;margin:34px 14px 10px;height:250px}
.p1-axe{position:absolute;left:0;right:0;top:120px;height:14px;border-radius:7px}
.p1-pt{position:absolute;top:0;height:250px;width:150px;transform:translateX(-50%)}
.p1-dot{position:absolute;left:50%;top:117px;transform:translateX(-50%);width:20px;height:20px;border-radius:50%;border:3px solid #000}
.p1-lbl{position:absolute;left:0;right:0}
.p1-pt.haut .p1-lbl{bottom:150px}.p1-pt.bas .p1-lbl{top:150px}
.p1-px{font-family:ui-monospace,monospace;font-size:21px;font-weight:700}
.p1-t{font-size:15px;color:var(--txt2);line-height:1.35}
.p1-echelle{font-size:14px;color:var(--gris);margin-top:-6px}
.p1-action{border:2px solid var(--p1-jaune);border-radius:24px;padding:38px 34px 30px;margin-top:26px;background:linear-gradient(160deg,rgba(242,207,91,.09),transparent 65%)}
.p1-av{font-size:32px;font-weight:600;margin:0 0 26px}
.p1-etape{margin:0 auto 26px;max-width:32em}.p1-etape:last-child{margin-bottom:0}
.p1-num{display:inline-flex;align-items:center;justify-content:center;width:38px;height:38px;border-radius:50%;background:var(--p1-jaune);color:#111;
font-family:ui-monospace,monospace;font-weight:700;font-size:18px;margin-bottom:8px}
.p1-etape p{margin:0;font-size:20px}
.p1-fin{color:var(--txt2);font-size:17px;margin-top:44px!important}
.p1-entree{margin-top:22px!important;padding:16px 20px;border:1px dashed rgba(242,207,91,.5);border-radius:14px;font-size:19px;max-width:none!important}
.tdb-titre{font-family:ui-monospace,monospace;letter-spacing:.2em;color:var(--cy);font-size:14px;margin:30px 0 16px}
@media(max-width:720px){body{font-size:18px}.p1{padding:40px 18px;font-size:18px}.p1-nom{font-size:32px}.p1-titre{font-size:28px}
.p1-duo{grid-template-columns:1fr}.p1-v{font-size:44px}.p1-regle,.p1-echelle{display:none}.p1-r,.p1-av{font-size:25px}.p1-chapeau{font-size:20px}}
"""


def main():
    if len(sys.argv) < 2:
        print(__doc__); sys.exit(1)
    argv = list(sys.argv)
    pf_chemin = None
    if '--pf' in argv:  # V24.1 : registre du portefeuille explicite
        i = argv.index('--pf')
        pf_chemin = argv[i + 1] if i + 1 < len(argv) else None
        del argv[i:i + 2]
    src = argv[1]
    out_dir = argv[3] if len(argv) > 3 and argv[2] == '-o' else os.path.dirname(os.path.abspath(src))
    base = os.path.splitext(os.path.basename(src))[0]
    if base.lower().startswith('dossier_'):
        base = base[len('dossier_'):]  # V22.8 : plus de prefixe Dossier_
    with open(src, encoding='utf-8') as f:
        brut = f.read()
    if src.lower().endswith(('.html', '.htm')):
        m = re.search(r'<script type="application/json" id="nico-source"[^>]*>(.*?)</script>', brut, re.S)
        if not m:
            print('Ce HTML ne contient pas de source NICO (dossier ant\u00e9rieur \u00e0 la V22.6).'); sys.exit(2)
        D = json.loads(m.group(1).replace('<\\/', '</'))
        base = base + '_relance'
        with open(os.path.join(out_dir, base + '.json'), 'w', encoding='utf-8') as f:
            json.dump(D, f, ensure_ascii=False, indent=1)
    else:
        D = json.loads(brut)
    D['_source'] = copy.deepcopy({k: v for k, v in D.items() if k != '_source'})
    R = calculer(D)
    calc_pourquoi(D, R)
    calc_avenir(D, R)
    calc_profil(D, R)     # V23 (A)
    calc_valeur(D, R)     # V23 (B)
    calc_capital(D, R)    # avant le contrôle d’autofinancement
    calc_autofinancement(D, R)
    calc_boule_neige(D, R)  # V23.6 : lecture des preuves, aucun effet financier
    _sur(calc_sources, D, R)  # V23.7 (C, D) : passe / consensus / guidance / central, escalier BPA-FCF
    _sur(calc_duree, D, R)    # V23.7 (B) : annees de croissance supposees par notre multiple et par le cours
    _sur(calc_monde, D, R)    # V23.7.1 : balance de ce que l'entreprise apporte au monde
    _sur(calc_longevite, R)   # V24 : longevite = annees exigees par le prix face aux annees visibles
    # ---- V24 : decider
    ticker_normalise(D, R)  # V25.1 : la place est convertie avant de chercher la ligne dans le registre
    if R.get('ticker'):
        D.setdefault('meta', {})['ticker'] = R['ticker']
    PF = charger_portefeuille(src, pf_chemin)
    lpf = ligne_du_portefeuille(D, PF)
    R['detenue'] = est_detenue(D, PF)
    _tac = [l for l in (PF or {}).get('lignes') or [] if _sans_accent(l.get('voie')).strip() in ('b', 'voie b')]
    R['pf'] = {'registre': (PF or {}).get('_chemin'), 'maj': (PF or {}).get('maj'), 'ligne': lpf,
               'tactiques': len(_tac) if PF and not PF['_incomplet'] else None,
               'tactique_ligne': lpf if lpf in _tac else None}
    _st = str(G(D, 'verdict.statut') or '').strip().upper()
    if PF is None:
        chk('Registre du portefeuille (V24.1)', 'n.d.', '%s introuvable : ligne détenue lue dans le JSON seulement' % PF_FICHIER)
        if R['detenue'] and not (D.get('meta') or {}).get('detenue'):
            warn('Statut PF ou mode réévaluation mais meta.detenue = false : ligne traitée comme DÉTENUE.')
    elif lpf:
        chk('Registre du portefeuille (V24.1)', 'alerte' if PF['_incomplet'] else 'validé', 'ligne détenue selon le registre du %s%s' % (
            PF.get('maj') or 'n.d.', (' · %s %% du portefeuille' % fr(_nb(lpf.get('poids_pct')), 1)) if num(_nb(lpf.get('poids_pct'))) else ''))
        _pr, _pj = _nb(lpf.get('poids_pct')), vv((D.get('meta') or {}).get('position_pct'))
        if num(_pr):
            if num(_pj) and abs(_pj - _pr) > 0.05:
                warn('Poids de la ligne : %s %% dans le JSON, %s %% dans le registre du %s — le registre fait foi.' % (
                    fr(_pj, 1), fr(_pr, 1), PF.get('maj') or 'n.d.'))
            D.setdefault('meta', {})['position_pct'] = _pr
    else:
        chk('Registre du portefeuille (V24.1)', 'alerte' if PF['_incomplet'] else 'validé',
            'aucune correspondance dans le registre du %s' % (PF.get('maj') or 'n.d.'))
        if _st == 'PF' or (D.get('meta') or {}).get('detenue'):
            warn('Le dossier dit « ligne détenue » (statut PF ou meta.detenue) mais %s ne la contient pas : mettre le registre à jour '
                 '(ou corriger le dossier). Ligne traitée comme détenue par prudence.' % PF_FICHIER)
    portes(D, R)
    _sur(calc_momentum_lecture, D, R)
    _sur(calc_fait_cle, D, R)
    _sur(calc_asymetrie, D, R)
    _sur(calc_voie_b, D, R)
    _sur(calc_confiance, D, R)
    _sur(calc_action, D, R)
    _sur(calc_angles_morts, D, R)
    _sur(calc_recit, D, R)  # V25 : le recit de la page 1 (lecture seule)
    nbm, nbp = compter_these(G(D, 'acte0.these.texte'))
    if nbm > 80 or not (3 <= nbp <= 4):
        warn('Th\u00e8se : %s mots / %s phrases \u2014 format 3 \u00e0 4 phrases, 80 mots au plus.' % (nbm, nbp))
    R['nico'] = ligne_nico(D, R)
    portes(D, R)
    hp = os.path.join(out_dir, base + '.html')
    with open(hp, 'w', encoding='utf-8') as f:
        f.write(rendu(D, R))
    with open(os.path.join(out_dir, base + '.calc.json'), 'w', encoding='utf-8') as f:
        json.dump({k: val for k, val in R.items() if k not in ('ctx', '_Bs')}, f, ensure_ascii=False, indent=1, default=str)
    print(resume(D, R))
    print('\nHTML : ' + hp)


if __name__ == '__main__':
    main()
