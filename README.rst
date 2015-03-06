Dependently Typed Koopa Troopas
===============================

Dit repository bevat de brontekst voor mijn populariserend artikel in verband
met mijn thesis: Programmeren en Bewijzen in Dependently Typed Talen.

Deze tekst is geschreven in reStructuredText en wordt met sphinx via latex
in een pdf omgezet. Als alles juist geconfigureerd is zou dit genoeg moeten
zijn om zelf een nieuwe pdf te genereren:

    | make latexpdf

De pdf is dan te vinden onder ``_build/latex/DependentlyTypedKoopaTroopas.pdf``.
Als je alleen de pdf nodig hebt:

    | cp _build/latex/DependentlyTypedKoopaTroopas.pdf .
    | make clean

