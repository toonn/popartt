======================================
    Dependently Typed KoopaTroopas
======================================

:Date: 2015-02
:Author: Toon Nolten
:Contact: <toon.nolten@student.kuleuven.be>

Wat zijn dependent types?
=========================

De meeste programmeertalen hebben types, e.g. voor gehele getallen,
voor vlottende-komma getallen.
Zulk een systeem kan ofwel sterk (statisch) ofwel zwak (dynamisch)
getypeerd zijn.
Programma's in statisch getypeerde talen kunnen niet in een bruikbare vorm
gebracht worden zonder dat alle typechecks slagen.
Programma's in dynamisch getypeerde talen daarentegen doen gewoon hun ding
tot er at runtime een typefout optreedt.
Dit klinkt natuurlijk goed, het programma kan werken ook al is het technisch
gezien niet helemaal juist maar de developer is vaak te ver verwijdert van zo'n
fout at runtime om ze gemakkelijk te kunnen oplossen.
In de praktijk wordt dit opgelost met uitgebreide testsuites maar zelfs dan
is er eigenlijk nooit de garantie dat het programma volledig juist is,
we kunnen immers niet alle mogelijke combinaties van invoer nagaan.

Een voorbeeld van een statisch typesysteem is het typesysteem van Java maar
ook Haskell heeft statische types ook al moeten we ze niet altijd schrijven
dankzij de type inference in het Hindley-Milner systeem.
Dependent types zijn een andere vorm van statische types.
Dit zijn types die kunnen afhangen van waardes (at runtime), e.g. de head
functie is meestal onveilig, ze mag eigenlijk niet toegepast worden op een
lege lijst, in een dependently typed taal kunnen we de lengte van lijsten bij
in hun type opnemen en dan kunnen we voor de head functie opleggen dat ze
enkel werkt op lijsten met een lengte verschillend van 0, dit soort lijsten
noemt men gewoonlijk vectors.
Dit voorbeeld is hieronder uitgewerkt in de taal Agda:

.. code-block:: agda
    data Vec (A : Set) : ℕ → Set where
      []  : Vec A zero
      _⸬_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
    
    head : {A : Set}{n : ℕ} → Vec A (suc n) → A
    head (x ⸬ xs) = x 
