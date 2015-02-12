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
functie [#head]_ is meestal onveilig, ze mag eigenlijk niet toegepast worden
op een lege lijst, in een dependently typed taal kunnen we de lengte van
lijsten bij in hun type opnemen en dan kunnen we voor de head functie
opleggen dat ze enkel werkt op lijsten met een lengte verschillend van 0,
dit soort lijsten noemt men gewoonlijk vectors.
Dit voorbeeld is hieronder uitgewerkt in de taal Agda [#agda]_:

.. code-block:: agda
    data Vec (A : Set) : ℕ → Set where
      []  : Vec A zero
      _⸬_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
    
    head : {A : Set}{n : ℕ} → Vec A (suc n) → A
    head (x ⸬ xs) = x 

Zoals we kunnen zien in het type van de head functie, werkt deze voor eender
welke vector met lengte *suc n*, de opvolger van een willekeurig natuurlijk
getal is altijd groter dan 0, dus lege vectors zijn niet toegelaten als
argument van de head functie.
Wat voor belang heeft dit nu?
In programma's met een onveilige head functie treedt er een fout op at runtime
wanneer ze wordt toegepast op een lege lijst.
Deze fout moet overal waar de functie gebruikt wordt, opgevangen worden anders
kan het programma crashen.
In een taal met dependent types kan je ervoor kiezen om statisch te garanderen
dat dit soort fouten zich nooit zal voordoen.
De prijs die je hiervoor betaalt is dat je types meer verboos worden.


Dependently typed Koopa Troopas
===============================

Om het nut van zulke statische verificatie duidelijker te maken heb ik een
uitgebreider voorbeeld uitgewerkt.
De meeste mensen kennen Mario wel, de dappere kleine loodgieter die het opneemt
tegen een legioen van onder meer paddestoelen en schildpadden om princes Peach
te redden van Bowser.
Die "schildpadden" zijn eigenlijk Koopa Troopas en ze komen in verschillende
kleuren en vormen voor.
Ik ga het hebben over de rode en de groene varianten.
De groene Koopa Troopas zijn tevens de bekendste, ze wandelen de hele tijd
in dezelfde richting waarbij ze van platforms afspringen zonder problemen
in tegenstelling tot hun rode variant, deze draaien om als ze aan het einde
van een platform komen [#koopa]_, beide keren ze wanneer ze een muur tegenkomen.
De mariospellen en zijn ook gekend vanwege de vele glitches [#glitch]_ die
erin voorkomen, deze worden veroorzaakt door fouten in het spelprogramma.
Fouten die met statische verificatie vermeden zouden kunnen worden.

In het voorbeeld laat ik zien hoe we het type van de Koopa Troopas kunnen
gebruiken om ervoor te zorgen dat een rode Koopa Troopa nooit van een platform
af zal lopen.
Ik laat enkel de code voor het pad type zien omdat dit het belangrijkste deel
van de oplossing is [#github]_:

.. code-block:: agda
    data Path {c : Color} (Koopa : KoopaTroopa c) :
         Position → Position → Set where
      []     : ∀ {p} → Path Koopa p p
      _↠〈_〉_ : {q r : Position} → (p : Position) → q follows p 〈 c 〉
                 → (qs : Path Koopa q r) → Path Koopa p r

.. Code uitleggen, voorbeelden laten zien, klaar is kees?


.. rubric:: Footnotes

.. [#head] De head functie geeft het eerste element van een lijst terug,
           dit is typisch een functie die men in functionele talen terugvindt,
           wat te danken is aan de recursieve structuur van lijsten in die
           talen. 
.. [#agda] Agda is een functionele taal met dependent types en een goed begin
           voor zij die geïnteresseerd zijn om zo'n taal uit te proberen.
           Dit artikel is een goed uitgangspunt: "Dependently Typed Programming
           in Agda, Ulf Norell and James Chapman."
.. [#koopa] In sommige spellen is er een ander verschil tussen de varianten.
.. [#glitch] In dit filmpje is te zien hoe iemand een fout in de code voor
             Koopa Troopas uitbuit om over de vlag aan het einde van het eerste
             level te springen: http://youtu.be/dzlmNdP-ApU
.. [#github] Voor zij die willen nagaan dat wat ik hier vertel geen gebakken
             lucht is; de code zowel voor het voorbeeld als voor dit artikel is
             hier beschikbaar: https://github.com/toonn/popartt
