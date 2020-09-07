## Agda installáció

Hivatalos dokumentáció installálásról: https://my-agda.readthedocs.io/en/latest/getting-started/installation.html 

Én a következőt ajánlom:

#### Ubuntu/Debian esetén: 

parancssorból `sudo apt-get install agda-mode`. Ez az Agda-t és az Emacs-ot is installálja.

#### Windows esetén: 

letölthető egy msi installer, ami elvileg mindent feltesz, amire szükség van: http://homepage.divms.uiowa.edu/~astump/agda/

#### Egyéb rendszer esetén azt tudom ajánlani, hogy fordítsunk Agda-t forrásból:

1. Installáljuk a Haskell stack-et: https://docs.haskellstack.org/en/stable/README/. Ez egy package manager Haskell-hez.
2. Parancssorban: először `stack setup`, ami installál egy GHC Haskell fordítót, azután `stack install Agda`, ami Agda-t fordít.
   Ha a második parancs hibát ad, akkor `stack install alex happy cpphs` után próbáljuk újra. A fordítás 10-20 percig tarthat.
3. Installáljuk az emacs-ot. 
4. Parancssorból: `agda-mode setup`. Ez beállítja az Agda emacs módját.

## Agda parancsok, unicode szimbólumok

Dokumentáció emacs parancsokról és unicode bevitelről: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html

## Alap Emacs parancsok

Lásd: https://www.cs.colostate.edu/helpdocs/emacs.html

## Hogyan kell Emacs-ban visszalépni az Agda unicode beviteli módba

`Alt-x`
`set-input-method`
`Agda`

## BEAD feladat megoldásának menete:

1. Másoljuk a kódrészletet saját gépre, `modulnév.agda` nevű fájlba, ahol a modulnév egyezik a kódrészletben látottal.
2. Definiáljuk a ?-eket.
3. Másoljuk a megoldást vissza a BEAD "megoldás" dobozba.

## Szép unicode font beállítása Emacs-ban:

1. Menüsor -> Options -> Set Default Font -> DejaVu Sans Mono (többféle is lehet ebből, és a Book variánst ajánlom)
2. Menüsor -> Options -> Save Options


