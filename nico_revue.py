"""Revue NICO en lot. Les valorisations sont calculées par nico.py."""
import argparse
import calendar
import copy
import datetime
import html
import hashlib
import json
import math
import os
import re
from collections import Counter
from pathlib import Path
from tempfile import NamedTemporaryFile

COMPLET = 'Revue complète'
A_VALIDER = 'À valider'
A_DOCUMENTER = 'À documenter'
CIBLEE = 'Mise à jour ciblée'
RAPIDE = 'Contrôle rapide'
PRIORITE = (COMPLET, A_VALIDER, A_DOCUMENTER, CIBLEE, RAPIDE)
ISSUE = {'renforcee': 'Renforcée', 'inchangee': 'Inchangée', 'fragilisee': 'Fragilisée', 'a_verifier': 'À vérifier'}


def objet(v, nom):
    if not isinstance(v, dict):
        raise ValueError(f'{nom} doit être un objet JSON')
    return v


def chaine(v, nom):
    if not isinstance(v, str) or not v.strip():
        raise ValueError(f'{nom} doit être renseigné')
    return v.strip()


def jour(v, nom):
    try:
        texte = chaine(v, nom)
        d = datetime.date.fromisoformat(texte)
        if d.isoformat() != texte:
            raise ValueError
        return d
    except ValueError as exc:
        raise ValueError(f'{nom} doit être une date ISO AAAA-MM-JJ') from exc


def nombre(v):
    return type(v) in (int, float) and math.isfinite(v)


def positif(v):
    return nombre(v) and v > 0


def lire_json(p):
    def non_fini(v):
        raise ValueError(f'Nombre non fini : {v}')
    return json.loads(p.read_text(encoding='utf-8-sig'), parse_constant=non_fini)


def fusionner(base, patch):
    """Applique un objet récursivement. Listes et null sont des remplacements explicites."""
    for cle, valeur in patch.items():
        if isinstance(valeur, dict) and isinstance(base.get(cle), dict):
            fusionner(base[cle], valeur)
        else:
            base[cle] = copy.deepcopy(valeur)


def jour_dossier(nico, valeur):
    # Les dossiers historiques acceptent des suffixes comme « clôture » ou « différé ».
    texte = str(nico.vv(valeur) or '').strip()
    date = re.match(r'^(\d{4}-\d{2}-\d{2}|\d{1,2}[/.-]\d{1,2}[/.-]\d{4})(?!\d)', texte)
    return nico._date_complete(date.group(1)) if date else None


def identite(nico, dossier):
    meta = objet(dossier.get('meta'), 'meta')
    ticker = {}
    nico.ticker_normalise(dossier, ticker)
    return (chaine(ticker.get('ticker') or meta.get('ticker'), 'meta.ticker').upper(),
            chaine(meta.get('devise'), 'meta.devise'))


def ligne_archivee(path):
    if path.suffix.lower() not in ('.html', '.htm'):
        return None, None
    texte = path.read_text(encoding='utf-8-sig')
    nico = re.search(r'<textarea\b[^>]*id=["\']nico-tri-copie["\'][^>]*>(.*?)</textarea>|'
                     r'<div\b[^>]*class=["\']nico["\'][^>]*>\s*(NICO\s*\|[^<]*)</div>', texte, re.S)
    action = re.search(r'<aside\b[^>]*class="c rail-conclusion"[^>]*>\s*<h2>.*?</h2>\s*<span\b[^>]*>(.*?)</span>',
                       texte, re.S)
    ligne = html.unescape((nico.group(1) or nico.group(2)).strip()) if nico else None
    consigne = html.unescape(re.sub(r'<[^>]+>', '', action.group(1))).strip() if action else None
    return ligne, consigne


def seuil(nico, calc):
    tactique = nico.G(calc, 'pf.tactique_ligne') or {}
    objectif = nico._nb(tactique.get('objectif'))
    if positif(objectif):
        return 'Objectif tactique', objectif, True
    if nico.G(calc, 'action.act') in ('ACHAT TACTIQUE (VOIE B)', 'RENFORCER TACTIQUEMENT (VOIE B)',
                                     'ATTENDRE LE SIGNAL (VOIE B)', 'SURVEILLER (VOIE B HORS ZONE)'):
        if nico.G(calc, 'voie_b.statut') in ('EN ATTENTE', 'HORS ZONE'):
            declencheur = nico.G(calc, 'voie_b.declencheur')
            return 'Signal tactique', declencheur if positif(declencheur) else None, True
        limite = nico.G(calc, 'voie_b.plafond')
        return 'Plafond tactique', limite if positif(limite) else None, False
    prix = calc.get('PA')
    actions = ('ACHETER', 'ACHETER (POCHE PARI)', 'ATTENDRE LE PRIX', 'RENFORCER',
               'RENFORCER (POCHE PARI)', 'GARDER — TAILLE ATTEINTE', 'GARDER, NE PAS RENFORCER')
    if not nico.G(calc, 'action.dossier_a_corriger') and nico.G(calc, 'action.act') in actions and positif(prix):
        return 'Plafond NICO', prix, False
    return '', None, False


def instantane(nico, d, r):
    texte = r.get('nico')
    if not isinstance(texte, str) or len(texte.split(' | ')) != 19:
        raise ValueError('Ligne TRI de calcul invalide : 19 champs attendus')
    p = texte.split(' | ')
    actif = nico.G(r, 'actifs.actif')
    pari = nico.G(r, 'pari.actif')
    route = ('Hors périmètre' if r.get('exclusion') else 'Assurance or' if r.get('assurance_or')
             else 'Actifs' if actif else 'Poche pari' if pari else 'Voie B' if nico.G(r, 'pf.tactique_ligne')
             else 'Voie A')
    return dict(action=nico.G(r, 'action.act') or 'À valider', statut=p[4], detenue=bool(r.get('detenue')),
                prix=r.get('PA') if positif(r.get('PA')) else None,
                rendement=r.get('retenu') if nombre(r.get('retenu')) else None, route=route, tri=texte,
                date=d['meta'].get('date_eval'), cours=nico.vv(nico.G(d, 'meta.cours')),
                baissier=(nico.G(r, 'actifs.cap') if actif else r.get('cap_cours')))


def marche_verifiee(v, date, devise, date_reference):
    marche = objet(v, 'marche')
    d = jour(marche.get('date'), 'marche.date')
    if date_reference and d < date_reference:
        raise ValueError(f'Cours fourni le {d.isoformat()}, antérieur au cours de référence du {date_reference.isoformat()}')
    if d > date:
        raise ValueError(f'Cours fourni le {d.isoformat()}, postérieur à la revue du {date.isoformat()}')
    if chaine(marche.get('devise'), 'marche.devise') != devise:
        raise ValueError(f'Devise de marché différente du dossier ({devise})')
    if not positif(marche.get('cours')):
        raise ValueError('marche.cours doit être un nombre positif')
    return dict(date=d.isoformat(), cours=marche['cours'], devise=devise, source=chaine(marche.get('source'), 'marche.source'))


def dernier_controle(v, date):
    veille = objet(v, 'veille')
    controle = jour(veille.get('date'), 'veille.date')
    if controle > date or 'publication' not in veille:
        raise ValueError('veille doit dater le contrôle et indiquer la publication, ou null si aucune n’a été trouvée')
    source = chaine(veille.get('source'), 'veille.source')
    publication = veille['publication']
    if publication is not None:
        pub = objet(publication, 'veille.publication')
        publiee = jour(pub.get('date'), 'veille.publication.date')
        if publiee > controle:
            raise ValueError('Une publication doit être antérieure ou égale à la date du contrôle')
        publication = dict(date=publiee.isoformat(), periode=chaine(pub.get('periode'), 'veille.publication.periode'),
                           source=chaine(pub.get('source'), 'veille.publication.source'))
        revision = pub.get('revision', 0)
        if type(revision) is not int or revision < 0:
            raise ValueError('Révision de publication invalide')
        if revision:
            publication['revision'] = revision
    return dict(date=controle.isoformat(), source=source, publication=publication)


def comparer_previsions(previsions, observations, date):
    if not isinstance(previsions, list) or not isinstance(observations, list):
        raise ValueError('suivi.previsions et observations doivent être des listes')
    refs, realises = {}, {}
    for nom, donnees, index in (('Prévision', previsions, refs), ('Observation', observations, realises)):
        for item in donnees:
            objet(item, nom)
            cle = (chaine(item.get('id'), nom + '.id'), chaine(item.get('periode'), nom + '.periode'),
                   chaine(item.get('unite'), nom + '.unite'))
            if cle in index:
                raise ValueError(f'{nom} en double pour {cle[0]} · {cle[1]} · {cle[2]}')
            index[cle] = item
    tableau = []
    for cle in dict.fromkeys((*refs, *realises)):
        prev, obs = refs.get(cle), realises.get(cle)
        date_prev = jour(prev.get('date'), 'prévision.date') if prev else None
        date_obs = jour(obs.get('date'), 'observation.date') if obs else None
        if (date_prev and date_prev > date) or (date_obs and date_obs > date):
            raise ValueError('Une prévision ou observation ne peut pas être postérieure à la revue')
        bas = prev.get('bas', prev.get('attendu')) if prev else None
        haut = prev.get('haut', prev.get('attendu')) if prev else None
        valeur = obs.get('valeur') if obs else None
        if prev and (not nombre(bas) or not nombre(haut) or bas > haut):
            raise ValueError(f'Fourchette invalide pour {cle[0]}')
        if obs:
            chaine(obs.get('source'), 'observation.source')
            if not nombre(valeur):
                raise ValueError(f'Observation non chiffrée pour {cle[0]}')
        if not prev:
            etat = 'Prévision absente'
        elif not obs:
            etat = 'Réalisé non renseigné'
        elif date_prev >= date_obs:
            etat = 'Prévision postérieure ou du jour · comparaison écartée'
        else:
            etat = 'Sous la fourchette' if valeur < bas else 'Au-dessus de la fourchette' if valeur > haut else 'Dans la fourchette'
        tableau.append(dict(id=cle[0], indicateur=(prev or obs).get('indicateur') or cle[0], periode=cle[1], unite=cle[2],
                            bas=bas, haut=haut, realise=valeur, etat=etat, prevision=date_prev.isoformat() if prev else None,
                            date_realise=date_obs.isoformat() if obs else None, source=obs.get('source') if obs else None))
    return tableau


def prix_personnel(v, date, devise):
    p = objet(v, 'prix_personnel')
    if p.get('devise') != devise or not positif(p.get('prix')):
        raise ValueError('Le prix personnel doit être positif et dans la devise du dossier')
    d = jour(p.get('date'), 'prix_personnel.date')
    if d > date:
        raise ValueError('Le prix personnel ne peut pas être postérieur à la revue')
    resultat = dict(prix=p['prix'], date=d.isoformat(), devise=devise, motif=chaine(p.get('motif'), 'prix_personnel.motif'),
                    hypotheses=p.get('hypotheses'), etat='À revalider sur les nouveaux chiffres')
    for k in ('empreinte_hypotheses', 'prix_nico'):
        if k in p:
            resultat[k] = p[k]
    return resultat


def variation_plafond(nico, d, src, registre, reference, courant):
    """Rejoue la référence à la nouvelle date, puis mesure le solde des changements."""
    if (reference['route'] != courant['route'] or
            not all(positif(x['prix']) for x in (reference, courant))):
        return None
    initiale = jour_dossier(nico, reference['date'])
    nouvelle = jour_dossier(nico, courant['date'])
    if not (initiale and nouvelle):
        return None
    if initiale == nouvelle:
        apres_temps = reference['prix']
    else:
        temoin = copy.deepcopy(d)
        temoin['meta']['date_eval'] = nouvelle.isoformat()
        alertes, controles = list(nico.WARN), list(nico.CHK)
        try:
            calcul = nico.traiter_dossier(temoin, str(src), registre)
            s = instantane(nico, temoin, calcul)
            apres_temps = s['prix'] if s['route'] == reference['route'] else None
        finally:
            nico.WARN[:], nico.CHK[:] = alertes, controles
    if not positif(apres_temps):
        return None
    return dict(reference=reference['prix'], temps=apres_temps - reference['prix'],
                autres=courant['prix'] - apres_temps, jours=(nouvelle - initiale).days)


def comparer_performance(entree, date):
    """Compare deux séries de rendement total dans une devise commune."""
    retours = entree.get('performance', [])
    if not isinstance(retours, list):
        raise ValueError('performance doit être une liste')
    lignes, vus = [], set()
    for p in retours:
        objet(p, 'performance')
        debut, fin = jour(p.get('debut'), 'performance.debut'), jour(p.get('fin'), 'performance.fin')
        mois = p.get('mois')
        nature = p.get('nature')
        if type(mois) is not int or mois not in (12, 24, 48) or nature not in ('execute', 'ecarte'):
            raise ValueError('performance attend un horizon 12, 24 ou 48 mois et une décision execute ou ecarte')
        annee, m = divmod(debut.year * 12 + debut.month - 1 + mois, 12)
        cible = datetime.date(annee, m + 1, min(debut.day, calendar.monthrange(annee, m + 1)[1]))
        if not cible <= fin <= min(cible + datetime.timedelta(days=7), date):
            raise ValueError('performance doit arriver à échéance et finir au plus sept jours après la date cible')
        cle = (debut, mois, nature)
        if cle in vus:
            raise ValueError('Mesure de performance en double')
        vus.add(cle)
        valeurs = [p.get(k) for k in ('titre_debut', 'titre_fin', 'iwda_debut', 'iwda_fin')]
        if not all(positif(x) for x in valeurs) or p.get('rendement_total') is not True:
            raise ValueError('performance attend quatre niveaux de rendement total positifs et comparables')
        t0, t1, b0, b1 = valeurs
        rt, rb = 100 * (t1 / t0 - 1), 100 * (b1 / b0 - 1)
        if not (nombre(rt) and nombre(rb) and nombre(rt - rb)):
            raise ValueError('Niveaux de performance hors limites')
        lignes.append(dict(debut=debut.isoformat(), fin=fin.isoformat(), mois=mois, nature=nature,
                           devise=chaine(p.get('devise'), 'performance.devise'), titre_pct=rt,
                           iwda_pct=rb, ecart_pts=rt - rb, source=chaine(p.get('source'), 'performance.source')))
    return lignes


def prochain_evenement(entree, date):
    calendrier = entree.get('prochaine_publication')
    if calendrier is None:
        return None
    p = objet(calendrier, 'prochaine_publication')
    quand = jour(p.get('date'), 'prochaine_publication.date')
    return dict(date=quand.isoformat(), source=chaine(p.get('source'), 'prochaine_publication.source'),
                etat='Passée · communiqué à rechercher' if quand < date else 'À venir',
                estimee=p.get('estimee') is True)


def calendrier_ics(bilan):
    def echapper(valeur):
        return str(valeur).replace('\\', '\\\\').replace('\n', '\\n').replace('\r', '').replace(',', '\\,').replace(';', '\\;')

    def plier(ligne):
        resultat = []
        while len(ligne.encode('utf-8')) > 75:
            index = 75
            while len(ligne[:index].encode('utf-8')) > 75:
                index -= 1
            resultat.append(ligne[:index])
            ligne = ' ' + ligne[index:]
        return resultat + [ligne]

    lignes = ['BEGIN:VCALENDAR', 'VERSION:2.0', 'PRODID:-//NICO//Revue//FR', 'CALSCALE:GREGORIAN']
    date_lot = bilan['date'].replace('-', '')
    for dossier in bilan['dossiers']:
        evenement = dossier.get('prochaine_publication')
        if not evenement or evenement['date'] < bilan['date']:
            continue
        date = evenement['date'].replace('-', '')
        identite_evenement = json.dumps([dossier['ticker'], dossier['devise'], evenement['date']])
        uid = hashlib.sha256(identite_evenement.encode()).hexdigest()[:24] + '@nico'
        titre = 'Publication ' + dossier['ticker'] + (' (estimée)' if evenement['estimee'] else '')
        lignes.extend(('BEGIN:VEVENT', 'UID:' + uid, 'DTSTAMP:' + date_lot + 'T000000Z',
                       'DTSTART;VALUE=DATE:' + date, 'SUMMARY:' + echapper(titre),
                       'STATUS:' + ('TENTATIVE' if evenement['estimee'] else 'CONFIRMED'),
                       'DESCRIPTION:' + echapper(evenement['source']), 'END:VEVENT'))
    if len(lignes) == 4:
        return None
    lignes.append('END:VCALENDAR')
    return '\r\n'.join(p for ligne in lignes for p in plier(ligne)) + '\r\n'


def donnees_par_instrument(chemin):
    if not chemin:
        return {}
    donnees = lire_json(chemin)
    if not isinstance(donnees, list):
        raise ValueError('Le fichier de données doit contenir une liste')
    resultats = {}
    for ligne in donnees:
        objet(ligne, 'données par instrument')
        cle = (chaine(ligne.get('ticker'), 'ticker').upper(), chaine(ligne.get('devise'), 'devise'))
        if cle in resultats:
            raise ValueError('Instrument en double dans les données · %s %s' % cle)
        resultats[cle] = {k: ligne[k] for k in ('marche', 'veille', 'prochaine_publication') if k in ligne}
    return resultats


def index_prix_personnels(chemins, date):
    prix = {}
    for chemin in chemins or []:
        brut = lire_json(chemin)
        entree = objet(brut, 'prix personnel exporté')
        if entree.get('schema') != 'nico-prix-personnel-1':
            raise ValueError('Fichier de prix personnel non reconnu')
        cle = (chaine(entree.get('ticker'), 'prix_personnel.ticker').upper(),
               chaine(entree.get('devise'), 'prix_personnel.devise'))
        p = prix_personnel(entree, date, cle[1])
        if cle in prix and prix[cle]['date'] == p['date'] and prix[cle] != p:
            raise ValueError('Prix personnels contradictoires pour %s %s' % cle)
        if cle not in prix or prix[cle]['date'] <= p['date']:
            prix[cle] = p
    return prix


def precedents_journal(journal, date):
    if not journal:
        return {}
    precedents = {}
    for p in sorted(journal.glob('revue_*.json')):
        revue = lire_json(p)
        if jour(revue.get('date'), 'date du journal') >= date:
            continue
        for x in revue['dossiers']:
            cle = (x['ticker'], x['devise'])
            # En cas de deux revues du même jour, ne pas arbitrer par ordre de hash.
            old = precedents.get(cle)
            valeur = x.get('prix_personnel')
            if old and old[0] == revue['date'] and old[1] != valeur:
                precedents[cle] = (revue['date'], None)
            else:
                precedents[cle] = (revue['date'], valeur)
    return {k: {'prix_personnel': p} for k, (_, p) in precedents.items()}


def journaliser(nico, journal, bilan):
    journal.mkdir(parents=True, exist_ok=True)
    contenu = encoder(nico, bilan)
    empreinte = hashlib.sha256(contenu.encode()).hexdigest()[:20]
    p = journal / f'revue_{bilan["date"]}_{empreinte}.json'
    if p.exists() and p.read_text(encoding='utf-8') != contenu:
        raise ValueError('Conflit dans le journal de revue')
    if not p.exists():
        ecrire_atomique(p, contenu)


def analyser_ligne(nico, entree, date, racine, pf, proximite, precedents, donnees=None, prix_importes=None):
    src = racine / chaine(entree.get('reference'), 'reference')
    d = objet(nico.lire_dossier(src), 'dossier de référence')
    ticker, devise = identite(nico, d)
    cle = (ticker, devise)
    if donnees:
        entree = {**donnees.get(cle, {}), **entree}
    nom = nico.G(d, 'meta.societe') or ticker
    date_ref = jour_dossier(nico, nico.G(d, 'meta.date_eval'))
    if date_ref and date_ref > date:
        raise ValueError('Le dossier de référence est postérieur à la revue')
    base = copy.deepcopy(d)
    registre_ref = str(racine / entree['registre_reference']) if entree.get('registre_reference') else None
    calc_ref = nico.traiter_dossier(base, str(src), registre_ref)
    ref = instantane(nico, base, calc_ref)
    archive, action_archivee = ligne_archivee(src)
    champs = archive.split(' | ') if archive else []
    archive_valide = (16 <= len(champs) <= 19 and champs[0] == 'NICO'
                      and champs[1].upper() == ticker and champs[3] == devise)
    ref_calculee = dict(ref)
    if archive_valide:
        ref['tri'] = archive
        ref['statut'] = champs[4]
        ref['detenue'] = champs[4] == 'PF'
        ref['prix'] = nico._nb(champs[5])
        ref['rendement'] = nico._nb(champs[8])
        if action_archivee:
            ref['action'] = action_archivee
    provenance_reference = 'Ligne TRI archivée' if archive_valide else 'Référence recalculée'
    marche = marche_verifiee(entree['marche'], date, devise, jour_dossier(nico, nico.G(d, 'meta.date_cours'))) if 'marche' in entree else None
    veille = dernier_controle(entree['veille'], date) if 'veille' in entree else None
    pub = veille.get('publication') if veille else None
    pub_ref = jour_dossier(nico, nico.G(d, 'resultats.publication.date'))
    date_veille = jour(pub['date'], 'publication') if pub else None
    probablement_couverte = bool(date_veille and not pub_ref and date_ref and date_veille <= date_ref)
    periode_ref = str(nico.G(d, 'resultats.publication.periode') or '').strip()
    revision_ref = nico.G(d, 'resultats.publication.revision', 0)
    if type(revision_ref) is not int or revision_ref < 0:
        raise ValueError('Révision de publication invalide dans le dossier de référence')
    meme_publication = pub and date_veille == pub_ref and pub['periode'] == periode_ref
    revision = pub.get('revision', 0) if pub else 0
    corrigee = bool(meme_publication and revision > revision_ref)
    nouvelle = bool(date_veille and not probablement_couverte and (
        not pub_ref or date_veille > pub_ref or (date_veille == pub_ref and pub['periode'] != periode_ref) or corrigee))
    publication_integree = False
    variation = None
    changements = entree.get('changements', [])
    if not isinstance(changements, list) or len(changements) > 3:
        raise ValueError('changements doit contenir au plus trois faits')
    faits = []
    for changement in changements:
        objet(changement, 'changement')
        faits.append({k: chaine(changement.get(k), 'changement.' + k) for k in ('fait', 'impact', 'source')})
    these = entree.get('these')
    if these is not None:
        objet(these, 'these')
        if these.get('etat') not in ISSUE:
            raise ValueError('État de thèse inconnu')
        these = dict(etat=ISSUE[these['etat']], motif=chaine(these.get('motif'), 'these.motif'))
    calc, courant = calc_ref, ref
    candidat = d
    actualisation = entree.get('actualisation')
    if actualisation is not None:
        actualisation = objet(actualisation, 'actualisation')
        if not actualisation:
            raise ValueError('actualisation est vide')
        if '_source' in actualisation:
            raise ValueError('actualisation._source est réservé au moteur')
        candidat = copy.deepcopy(d)
        fusionner(candidat, actualisation)
        pub_patch = nico.G(actualisation, 'resultats.publication')
        nouvelle_identite_pub = (jour_dossier(nico, nico.G(candidat, 'resultats.publication.date')),
                                 nico.G(candidat, 'resultats.publication.periode'))
        if (isinstance(pub_patch, dict) and 'revision' not in pub_patch
                and nouvelle_identite_pub != (pub_ref, periode_ref)):
            candidat['resultats']['publication'].pop('revision', None)
        if identite(nico, candidat) != (ticker, devise):
            raise ValueError('L’actualisation doit conserver le même instrument et la même devise')
        if marche:
            candidat['meta'].update(cours=marche['cours'], date_cours=marche['date'])
        date_eval = jour_dossier(nico, nico.G(candidat, 'meta.date_eval'))
        date_pub = jour_dossier(nico, nico.G(candidat, 'resultats.publication.date'))
        date_cours = jour_dossier(nico, nico.G(candidat, 'meta.date_cours'))
        if not date_eval or date_eval > date or (date_ref and date_eval < date_ref):
            raise ValueError('L’actualisation doit dater l’évaluation entre la référence et la revue')
        if any(x and x > date_eval for x in (date_pub, date_cours)):
            raise ValueError('Cours ou publication postérieur à l’évaluation : actualiser meta.date_eval')
        if pub_ref and (not date_pub or date_pub < pub_ref):
            raise ValueError('L’actualisation ne peut pas supprimer ou antidater la publication de référence')
        calc = nico.traiter_dossier(candidat, str(src), pf)
        courant = instantane(nico, candidat, calc)
        revision_candidat = nico.G(candidat, 'resultats.publication.revision', 0)
        if (type(revision_candidat) is not int or revision_candidat < 0
                or (date_pub == pub_ref and nico.G(candidat, 'resultats.publication.periode') == periode_ref
                    and revision_candidat < revision_ref)):
            raise ValueError('L’actualisation ne peut pas antidater une révision de publication')
        if (date_veille and date_pub == date_veille and nico.G(candidat, 'resultats.publication.periode') == pub['periode']
                and revision_candidat == revision):
            publication_integree = True
        variation = variation_plafond(nico, d, src, registre_ref, ref_calculee, courant)

    risque = nico.risque_prioritaire(candidat)
    vigie = entree.get('prochain_test') or (nico.suivi_risque(risque) if risque else None)
    vigie = vigie or nico.G(candidat, 'verdict.suivi_condition')
    libelle, niveau, hausse = seuil(nico, calc)
    if not actualisation and ref['prix'] is not None and libelle == 'Plafond NICO':
        niveau = ref['prix']
    ecart = (marche['cours'] / niveau - 1) * 100 if marche and positif(niveau) else None
    atteint = (ecart >= 0 if hausse else ecart <= 0) if ecart is not None else False
    proche = ecart is not None and not atteint and abs(ecart) <= proximite
    echec = []
    if not veille:
        echec.append('Dernière publication non vérifiée')
    elif date_ref and jour(veille['date'], 'veille.date') < date_ref:
        echec.append('Contrôle de publication antérieur au dossier de référence')
    elif pub is None and pub_ref:
        echec.append('Publication non retrouvée malgré une référence existante')
    elif date_veille and pub_ref and date_veille < pub_ref:
        echec.append('La publication fournie précède celle du dossier de référence')
    elif meme_publication and revision < revision_ref:
        echec.append('La révision fournie précède celle du dossier de référence')
    elif actualisation and pub and not publication_integree and not nouvelle and (pub_ref or date_pub):
        echec.append('Publication actualisée incohérente avec la veille')
    if not marche:
        echec.append('Cours daté non fourni')
    lourd = []
    if entree.get('motif_revue_complete'):
        lourd.append(chaine(entree['motif_revue_complete'], 'motif_revue_complete'))
    secteur = nico._sans_accent(nico.G(d, 'meta.secteur'))
    classification = nico.G(candidat, 'profil.actifs')
    if not classification and re.search(r'\b(mines?|minier(?:e)?s?|mining|petrole|oil\s*(?:and|&)\s*gas)\b', secteur):
        lourd.append('Route Actifs à vérifier avant migration du dossier')
    if actualisation:
        f = nico.G(calc, 'cash_action.financement')
        ancien_f = nico.G(calc_ref, 'cash_action.financement')
        if f and f != ancien_f and f['non_couvert_m'] > 0:
            lourd.append('Besoin de financement non couvert à examiner')
    if courant['route'] != ref['route']:
        lourd.append(f'Méthode modifiée : {ref["route"]} → {courant["route"]}')
    if these and these['etat'] == 'Fragilisée':
        lourd.append('Thèse fragilisée : ' + these['motif'])
    tactique = nico.G(calc, 'pf.tactique_ligne') or {}
    echeance = jour_dossier(nico, tactique.get('echeance'))
    if echeance and echeance < date:
        lourd.append(f'Échéance tactique dépassée le {echeance:%d/%m/%Y}')
    if atteint and libelle == 'Objectif tactique':
        lourd.append('Objectif de sortie tactique atteint')
    decision_a_valider = (courant['route'] == 'Voie A' and calc.get('calc') and
                          not nico.G(candidat, 'verdict.achat') and
                          courant['action'] == 'NE PAS ACHETER')
    if lourd:
        priorite, motifs = COMPLET, lourd + echec
    elif decision_a_valider:
        priorite, motifs = A_VALIDER, ['Avis analyste absent du dossier Voie A'] + echec
    elif echec:
        priorite, motifs = A_DOCUMENTER, echec
    elif nouvelle or atteint or proche or actualisation or faits or (these and these['etat'] == 'Renforcée'):
        priorite = CIBLEE
        motifs = (['Nouvelle publication intégrée' if publication_integree else 'Nouvelle publication à traiter'] if nouvelle else []) + (
            [libelle + (' atteint' if atteint else ' proche')] if atteint or proche else [])
        if not motifs:
            motifs = ['Dossier actualisé à partir du lot' if actualisation else 'Nouveaux éléments de thèse']
    elif probablement_couverte:
        priorite, motifs = RAPIDE, []
    else:
        priorite, motifs = RAPIDE, ['Aucun nouveau communiqué identifié' if veille['publication'] is None
                                    else 'Dernière publication déjà couverte']
    if corrigee:
        motifs.append('Révision officielle du communiqué · version %s' % revision)
    if probablement_couverte:
        motifs.append('Publication probablement couverte par le dossier de référence, à confirmer')
    ancien = precedents.get(cle, {}).get('prix_personnel')
    prix = entree.get('prix_personnel', (prix_importes or {}).get(cle, ancien))
    personne = prix_personnel(prix, date, devise) if prix is not None else None
    if personne and personne.get('empreinte_hypotheses') == calc.get('empreinte_hypotheses') and calc.get('empreinte_hypotheses'):
        personne['etat'] = 'Hypothèses de référence identiques'
    observations = entree.get('observations')
    if observations is None:
        p = nico.G(candidat, 'resultats.publication') or {}
        observations = [dict(k, date=date_veille.isoformat(), periode=pub['periode'], source=pub['source'])
                        for k in p.get('kpis', []) if isinstance(k, dict)] if publication_integree and isinstance(p.get('kpis'), list) else []
    previsions = comparer_previsions(nico.G(d, 'suivi.previsions') or [], observations, date)
    exportable = actualisation and priorite == CIBLEE and (not nouvelle or publication_integree)
    ligne = dict(ticker=ticker, societe=nom, devise=devise, priorite=priorite, motifs=motifs, veille=veille, marche=marche,
                 reference=ref, provenance_reference=provenance_reference, courant=courant if actualisation else None,
                 tri_actualise=courant['tri'] if exportable else None,
                 seuil=dict(nom=libelle, valeur=niveau, ecart_pct=ecart, atteint=atteint, proche=proche),
                 faits=faits, these=these, prochain_test=vigie, previsions=previsions, prix_personnel=personne,
                 publication_reference=pub_ref.isoformat() if pub_ref else None, nouvelle_publication=nouvelle,
                 publication_integree=publication_integree, fichier_reference=entree['reference'],
                 mode='Recalcul' if actualisation else 'Contrôle')
    for cle, valeur in (('variation_plafond', variation), ('prochaine_publication', prochain_evenement(entree, date)),
                        ('performance', comparer_performance(entree, date)), ('cash_action', calc.get('cash_action'))):
        if valeur:
            ligne[cle] = valeur
    if revision:
        ligne['revision_publication'] = revision
    return ligne, (candidat, calc) if exportable else None


def analyser_lot(nico, lot, racine, pf, sortie, donnees=None, prix_importes=None, journal=None):
    date = jour(lot.get('date'), 'date')
    proximite = lot.get('proximite_pct', 5)
    if not nombre(proximite) or not 0 <= proximite <= 100:
        raise ValueError('proximite_pct doit être compris entre 0 et 100')
    entrees = lot.get('dossiers')
    if not isinstance(entrees, list) or not entrees:
        raise ValueError('dossiers doit être une liste non vide')
    precedents = precedents_journal(journal, date)
    if lot.get('revue_precedente'):
        ancien = lire_json(racine / lot['revue_precedente'])
        if jour(ancien.get('date'), 'date de la revue précédente') >= date:
            raise ValueError('La revue précédente doit précéder le lot courant')
        precedents.update({(x['ticker'], x['devise']): x for x in ancien['dossiers']})
    lignes, erreurs, vus = [], [], set()
    for i, entree in enumerate(entrees, 1):
        try:
            ligne, dossier = analyser_ligne(nico, objet(entree, 'dossier'), date, racine, pf, proximite, precedents, donnees, prix_importes)
            identifiant = (ligne['ticker'], ligne['devise'])
            if identifiant in vus:
                raise ValueError(f'Instrument en double : {ligne["ticker"]} {ligne["devise"]}')
            vus.add(identifiant)
            if dossier:
                d, r = dossier
                nom = re.sub(r'[^a-zA-Z0-9_.-]', '_', '-'.join(identifiant))
                dossier_sortie = Path('dossiers_' + date.isoformat())
                (sortie / dossier_sortie).mkdir(exist_ok=True)
                html_path = dossier_sortie / f'{i:03d}_{nom}.html'
                json_path = html_path.with_suffix('.json')
                rendu = nico.rendu(d, r)
                ecrire_atomique(sortie / json_path, encoder(nico, d['_source']))
                ecrire_atomique(sortie / html_path, rendu)
                ligne.update(dossier_html=html_path.as_posix(), dossier_json=json_path.as_posix())
            lignes.append(ligne)
        except (ValueError, OSError, KeyError, TypeError, ArithmeticError) as exc:
            erreurs.append(dict(ligne=i, reference=entree.get('reference') if isinstance(entree, dict) else None, motif=str(exc)))
    def ordre(x):
        seuil_x = x['seuil']
        return (PRIORITE.index(x['priorite']), not x['reference']['detenue'], not seuil_x['atteint'],
                abs(seuil_x['ecart_pct']) if seuil_x['ecart_pct'] is not None else math.inf, x['ticker'])
    lignes.sort(key=ordre)
    return dict(version=nico.VERSION, date=date.isoformat(), proximite_pct=proximite, contexte=lot.get('contexte'),
                dossiers=lignes, erreurs=erreurs, nombre_entrees=len(entrees))


def ecrire_atomique(chemin, contenu):
    tmp = None
    try:
        with NamedTemporaryFile(mode='w', dir=chemin.parent, encoding='utf-8', newline='', delete=False) as flux:
            tmp = Path(flux.name)
            flux.write(contenu)
        os.replace(tmp, chemin)
    finally:
        if tmp is not None:
            tmp.unlink(missing_ok=True)


def encoder(nico, donnees):
    return json.dumps(nico._fini(donnees), indent=2, ensure_ascii=False, allow_nan=False) + '\n'


CSS = """
:root{color-scheme:dark;--bg:#101719;--surface:#162124;--line:#2e4146;--text:#e8f1ef;--muted:#a1b7b5;
--teal:#72e7c0;--red:#ff9c9f;--amber:#f3c37d;--blue:#a3d5ef;font:16px/1.55 "Instrument Sans",system-ui,sans-serif}
*{box-sizing:border-box}body{background:var(--bg);color:var(--text);margin:0}main{max-width:1180px;margin:auto;padding:36px 24px 72px}
h1,h2,h3,p,ul{margin:0}h1{font-size:clamp(2.15rem,5vw,3.75rem);line-height:1.04;letter-spacing:-.045em}
h2{font-size:1.42rem;letter-spacing:-.02em;margin:32px 0 12px}h3{font-size:1rem;margin:16px 0 8px}
p,.muted{color:var(--muted)}header p{margin:12px 0 0}a{color:var(--teal);text-underline-offset:.22em}
.metrics{display:flex;flex-wrap:wrap;gap:8px;margin:22px 0}.metrics span,.tag{border:1px solid var(--line);border-radius:20px;padding:4px 10px;font-size:.8rem}
.metrics span{white-space:nowrap}.tone-0{color:var(--red)}.tone-1,.tone-2{color:var(--amber)}.tone-3{color:var(--teal)}.tone-4{color:var(--blue)}
.scroller{overflow:auto;border:1px solid var(--line);border-radius:12px}table{width:100%;border-collapse:collapse;background:var(--surface)}
th,td{text-align:left;padding:11px 12px;vertical-align:top}th{color:var(--muted);font-size:.8rem;font-weight:650}td{border-top:1px solid var(--line)}
td .tag{display:inline-block;white-space:nowrap}td small{display:block;color:var(--muted)}tbody tr:hover{background:#1c2a2e}
details{border:1px solid var(--line);border-radius:12px;margin:10px 0;background:var(--surface)}
details summary{cursor:pointer;font-weight:650;padding:12px 16px}details .content{padding:0 16px 16px}
strong{color:var(--text)}.values{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:10px;margin:12px 0}
.values div{background:var(--bg);border-radius:8px;padding:9px 11px}.values span{display:block;color:var(--muted);font-size:.8rem}
ul{padding-left:20px}li+li{margin-top:5px}.content p+p{margin-top:7px}
textarea{width:100%;min-height:90px;resize:vertical;border:1px solid var(--line);border-radius:8px;padding:10px;background:var(--bg);color:var(--text)}
.copier-tri{font:inherit;background:var(--bg);color:var(--teal);border:1px solid var(--line);
border-radius:8px;padding:9px 12px;cursor:pointer}.copier-tri+span{margin-left:8px;font-size:.85rem}
.priorites .libelle-mobile{display:none}
@media(max-width:640px){main{padding:24px 15px 55px}th,td{padding:8px}.scroller table{min-width:660px}.content .scroller table{min-width:500px}}
@media(max-width:600px){
  .priorites{overflow:visible;border:0;border-radius:0}
  .priorites table,.priorites tbody{display:block;min-width:0;background:transparent}
  .priorites thead{position:absolute;width:1px;height:1px;overflow:hidden;clip-path:inset(50%)}
  .priorites tbody tr{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));margin-bottom:12px;
    border:1px solid var(--line);border-radius:12px;background:var(--surface);padding:4px}
  .priorites td{display:block;min-width:0;border:0;overflow-wrap:anywhere}
  .priorites td:nth-child(-n+3){grid-column:1/-1}
  .priorites td:nth-child(n+4){border-top:1px solid var(--line)}
  .priorites .libelle-mobile{display:block;color:var(--muted);font-size:.8rem}
  .priorites .tag{white-space:normal}
}
"""


def rendu_html(nico, bilan):
    e = html.escape

    def propre(v):
        return e(str(v)) if v not in (None, '') else 'n.d.'

    def prix(v, devise):
        return e(nico.fplafond(v, devise) + ' ' + devise) if positif(v) else 'n.d.'

    def cours(v, devise):
        return e(nico.fprix(v) + ' ' + devise) if positif(v) else 'n.d.'

    def variation(avant, apres, devise):
        p0, p1 = prix(avant, devise), prix(apres, devise)
        return p0 if p0 == p1 else f'{p0} → {p1}'

    def tag(priorite):
        return f'<span class="tag tone-{PRIORITE.index(priorite)}">{e(priorite)}</span>'

    colonnes = ('Société', 'Revue', 'Action du dossier', 'Cours fourni', 'Seuil à suivre', 'Dernière publication')
    tableau, fiches = [], []
    for i, x in enumerate(bilan['dossiers']):
        identifiant = f'dossier-{i + 1}'
        ref, c = x['reference'], x['courant']
        m, v, s = x['marche'], x['veille'], x['seuil']
        pub = v['publication'] if v else None
        recalcule = c or ref
        texte_action = propre(ref['action'])
        if c and c['action'] != ref['action']:
            texte_action += ' → ' + propre(c['action'])
        q = cours(m['cours'], x['devise']) if m else 'n.d.'
        date_cours = '<small>' + e(m['date']) + '</small>' if m else ''
        niveau = f'{e(s["nom"])} · {prix(s["valeur"], x["devise"])}' if positif(s['valeur']) else 'n.d.'
        distance = ''
        if s['ecart_pct'] is not None:
            distance = '<small>' + e(nico.fr(s['ecart_pct'], 1, True)) + ' %</small>'
        mot = ' · '.join(x['motifs'])
        cellules = (
            f'<a href="#{identifiant}"><strong>{e(x["ticker"])}</strong></a><small>{propre(x["societe"])}</small>',
            f'{tag(x["priorite"])}<small>{e(mot)}</small>',
            f'{texte_action}<small>{propre(recalcule["statut"])} · {propre(recalcule["route"])}</small>',
            q + date_cours, niveau + distance, propre(pub['date'] if pub else None),
        )
        ligne = []
        for index, (titre, valeur) in enumerate(zip(colonnes, cellules)):
            libelle = f'<span class="libelle-mobile" aria-hidden="true">{titre}</span>' if index >= 2 else ''
            ligne.append(f'<td role="cell">{libelle}{valeur}</td>')
        tableau.append('<tr role="row">' + ''.join(ligne) + '</tr>')
        description = f'<p>{e(x["provenance_reference"])} · {propre(ref["date"])} · {e(ref["route"])}</p>'
        if m:
            description += f'<p>Cours contrôlé le {e(m["date"])} · {e(m["source"])}</p>'
        if pub:
            description += f'<p>{e(pub["date"])} · {e(pub["periode"])} · {e(pub["source"])}</p>'
        if v:
            description += f'<p>Veille du {e(v["date"])} · {e(v["source"])}</p>'
        rendements = e(nico.fr(ref['rendement'], 1)) + ' %' if nombre(ref['rendement']) else 'n.d.'
        if c and c['rendement'] != ref['rendement']:
            rendements += ' → ' + (e(nico.fr(c['rendement'], 1)) + ' %' if nombre(c['rendement']) else 'n.d.')
        valeurs = (f'<div class="values"><div><span>Action du moteur</span><strong>{texte_action}</strong></div>'
                   f'<div><span>Plafond du dossier</span><strong>{variation(ref["prix"], recalcule["prix"], x["devise"])}</strong></div>'
                   f'<div><span>Rendement au cours du dossier</span><strong>{rendements}</strong></div></div>')
        faits = ''.join(f'<li><strong>{e(t["fait"])}</strong> · {e(t["impact"])}<br><small>{e(t["source"])}</small></li>' for t in x['faits'])
        contenu = description + valeurs
        effet = x.get('variation_plafond')
        if effet:
            contenu += ('<p>Variation à partir du prix recalculé · temps %s %s sur %s j · '
                        'autres changements %s %s.</p>') % (
                e(nico.fr(effet['temps'], 2, True)), e(x['devise']), effet['jours'],
                e(nico.fr(effet['autres'], 2, True)), e(x['devise']))
        evenement = x.get('prochaine_publication')
        if evenement:
            contenu += '<p>Prochaine publication · %s%s · %s · %s</p>' % (
                e(evenement['date']), ' (estimée)' if evenement['estimee'] else '',
                e(evenement['etat']), e(evenement['source']))
        cash = x.get('cash_action')
        if cash and cash.get('decisif'):
            contenu += nico.cash_action_html({'cash_action': cash}).replace(' id="cash-action"', '')
        perf = x.get('performance', [])
        if perf:
            lignes_perf = ''.join('<li>%s mois · %s · titre %s %% · IWDA %s %% · %s pts · %s</li>' % (
                p['mois'], e(p['nature']), e(nico.fr(p['titre_pct'], 1, True)), e(nico.fr(p['iwda_pct'], 1, True)),
                e(nico.fr(p['ecart_pts'], 1, True)), e(p['source'])) for p in perf)
            contenu += '<h3>Performance observée</h3><ul>' + lignes_perf + '</ul>'
        if faits:
            contenu += f'<h3>Ce qui a changé</h3><ul>{faits}</ul>'
        if x['these']:
            contenu += f'<h3>Effet sur la thèse</h3><p>{e(x["these"]["etat"])} · {e(x["these"]["motif"])}</p>'
        if x['prochain_test']:
            contenu += '<h3>Prochain test</h3><p>' + propre(x['prochain_test']) + '</p>'
        if x['previsions']:
            lignes = []
            for p in x['previsions']:
                plage = propre(p['bas']) if p['bas'] == p['haut'] else f'{propre(p["bas"])} à {propre(p["haut"])}'
                lignes.append(f'<tr><td>{propre(p["indicateur"])}<small>{e(p["periode"])} · {e(p["unite"])}</small></td>'
                              f'<td>{plage}<small>{propre(p["prevision"])}</small></td>'
                              f'<td>{propre(p["realise"])}<small>{propre(p["source"])}</small></td><td>{e(p["etat"])}</td></tr>')
            contenu += ('<h3>Notre prévision face au réalisé</h3><div class="scroller"><table><thead><tr>'
                        '<th>Indicateur</th><th>Prévision datée</th><th>Réalisé</th><th>Lecture</th></tr></thead>'
                        '<tbody>' + ''.join(lignes) + '</tbody></table></div>')
        if x['prix_personnel']:
            p = x['prix_personnel']
            contenu += f'<h3>Prix personnel</h3><p>{prix(p["prix"], p["devise"])} · {e(p["date"])} · {e(p["etat"])} · {e(p["motif"])}</p>'
        if x['tri_actualise']:
            contenu += (f'<h3><label for="tri-{i}">Ligne TRI actualisée</label></h3><textarea id="tri-{i}" readonly>{e(x["tri_actualise"])}</textarea>'
                        f'<button type="button" class="copier-tri" data-tri="tri-{i}">Copier la ligne TRI</button>'
                        f'<span id="etat-tri-{i}" role="status"></span>')
            if x.get('dossier_html'):
                contenu += (f'<p><a href="{e(x["dossier_html"])}">Ouvrir le dossier complet</a> · '
                            f'<a href="{e(x["dossier_json"])}">JSON de référence suivant</a></p>')
        fiches.append(f'<details id="{identifiant}"><summary>{e(x["ticker"])} · {propre(x["societe"])}</summary>'
                      f'<div class="content">{contenu}</div></details>')
    compte = Counter(x['priorite'] for x in bilan['dossiers'])
    compte_html = ''.join(f'<span class="tone-{i}">{compte[p]} · {e(p)}</span>' for i, p in enumerate(PRIORITE) if compte[p])
    erreurs = ''.join(f'<li>Ligne {x["ligne"]} · {propre(x["reference"])} · {e(x["motif"])}</li>' for x in bilan['erreurs'])
    if erreurs:
        erreurs = '<h2>Entrées à corriger</h2><ul>' + erreurs + '</ul>'
    contexte = '<p>' + propre(bilan['contexte']) + '</p>' if bilan['contexte'] else ''
    entetes = ''.join(f'<th scope="col" role="columnheader">{titre}</th>' for titre in colonnes)
    return (f'<!doctype html><html lang="fr"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>Revue trimestrielle NICO</title><style>{CSS}</style></head><body><main><header>'
            f'<h1>Revue trimestrielle</h1><p>NICO {e(bilan["version"])} · {e(bilan["date"])} · {len(bilan["dossiers"])} '
            f'dossiers sur {bilan["nombre_entrees"]}</p>{contexte}</header><div class="metrics">{compte_html}</div>'
            '<h2>Priorités du lot</h2><div class="scroller priorites"><table role="table"><thead role="rowgroup"><tr role="row">'
            + entetes + '</tr></thead><tbody role="rowgroup">' + ''.join(tableau) + '</tbody></table></div>' + erreurs
            + '<h2>Détail des sociétés</h2>' + ''.join(fiches) + '</main><script>'
            'function ouvrir(){const x=document.getElementById(location.hash.slice(1));if(x?.tagName==="DETAILS")x.open=true;}'
            'addEventListener("hashchange",ouvrir);ouvrir();'
            'document.querySelectorAll("[data-tri]").forEach(b=>b.addEventListener("click",async()=>{'
            'const t=document.getElementById(b.dataset.tri),s=document.getElementById("etat-"+t.id);'
            'try{await navigator.clipboard.writeText(t.value);s.textContent=" Ligne copiée.";}' 
            'catch{t.focus();t.select();s.textContent=" Ligne sélectionnée. Utilise Ctrl+C.";}}));'
            '</script></body></html>')


def main_revue(nico, arguments):
    parser = argparse.ArgumentParser(prog='nico.py revue', description='Compare les dossiers NICO à leurs actualisations.')
    parser.add_argument('lot', type=Path)
    parser.add_argument('-o', '--sortie', type=Path)
    parser.add_argument('--pf', type=Path, help='registre courant pour les dossiers actualisés')
    parser.add_argument('--donnees', type=Path, help='cours et publications fournis par instrument')
    parser.add_argument('--prix-perso', type=Path, action='append', help='fichier JSON exporté depuis les réglettes')
    parser.add_argument('--journal', type=Path, help='dossier local des revues historisées')
    args = parser.parse_args(arguments)
    try:
        lot = objet(lire_json(args.lot), 'lot')
        if args.pf and not args.pf.is_file():
            raise ValueError('Registre courant introuvable')
        sortie = args.sortie or args.lot.resolve().parent
        sortie.mkdir(parents=True, exist_ok=True)
        donnees = donnees_par_instrument(args.donnees)
        prix = index_prix_personnels(args.prix_perso, jour(lot.get('date'), 'date'))
        bilan = analyser_lot(nico, lot, args.lot.resolve().parent, str(args.pf.resolve()) if args.pf else None,
                            sortie, donnees, prix, args.journal)
        base = sortie / ('Revue_NICO_' + bilan['date'])
        ecrire_atomique(base.with_suffix('.json'), encoder(nico, bilan))
        ecrire_atomique(base.with_suffix('.html'), rendu_html(nico, bilan))
        calendrier = calendrier_ics(bilan)
        if calendrier:
            ecrire_atomique(base.with_suffix('.ics'), calendrier)
        else:
            base.with_suffix('.ics').unlink(missing_ok=True)
        if args.journal:
            journaliser(nico, args.journal, bilan)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        parser.error(str(exc))
    print(f'{len(bilan["dossiers"])} dossiers · {len(bilan["erreurs"])} entrées à corriger')
    print(base.with_suffix('.html'))
    print(base.with_suffix('.json'))
    if calendrier:
        print(base.with_suffix('.ics'))
    if bilan['erreurs']:
        raise SystemExit(1)
