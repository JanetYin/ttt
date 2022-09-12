(1) Töltsük le a GHCupon keresztül a Haskell eszközeit az alábbi paranccsal (egy __nem__ admin PowerShellbe bemásolva):

```Set-ExecutionPolicy Bypass -Scope Process -Force;[System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072;Invoke-Command -ScriptBlock ([ScriptBlock]::Create((Invoke-WebRequest https://www.haskell.org/ghcup/sh/bootstrap-haskell.ps1 -UseBasicParsing))) -ArgumentList $true```

Amikor kérdezget, fogadjuk el az alapértelmezéseket.

(2) Miközben a GHCup telepít, töltsük le az Emacs szövegszerkesztőt innen: http://quantum-mirror.hu/mirrors/pub/gnu/emacs/windows/emacs-28/emacs-28.1-installer.exe
Letöltés után telepítsük.

(3) Ha készen van a GHCup, adjuk hozzá a Pathhez a haskelles binárisokat, hogy a parancssorból egyszerűbben lehessen őket futtatni. A Path változót így lehet megtalálni: https://www.h3xed.com/windows/how-to-add-to-and-edit-windows-path-variable
Ehhez adjuk hozzá a ```C:\ghcup\bin``` mappát (vagy ahol a binárisok vannak, ha nem a default helyre telepítettünk).

(4) Zárjunk be minden gépházas ablakot és indítsuk újra a PowerShellt.

(5) Futtassuk le az alábbi parancsokat a telepítéshez:

```cabal update```

```cabal install Agda```

Ez meglehetősen hosszú idő szokott lenni (fél-egy óra).

(6) Adjuk hozzá a Pathhez a ```C:\cabal\bin``` és a ```C:\Program Files\Emacs\emacs-28.1\bin``` mappákat is (hasonlóan, mint az előbb).

(7) Megint zárjunk be minden gépházas ablakot és indítsuk újra a PowerShellt.

(8) Az Emacs Agda-módjának telepítéséhez futtassuk le az alábbi parancsot:

```agda-mode setup```

(9) Teszteléshez indítsuk el az Emacset így:

```emacs test.agda```

Ha az ablak fejlécén van Agda menü, akkor készen vagyunk:)
