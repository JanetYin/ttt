open import Lib

-- A **nulladrendű logikához** nézd meg a gy08 elején és a gy07 végén levő deces feladatokat.
-- Lehet bizonyítós meg ellenpéldás is.

-- Érdekesség: próbáld meg ezt kikommentelni; mi történik?
a : ℕ
a = 5

-- Fontos: ilyen jellegű feladat a vizsgán **nem** lesz;
-- csak röpin.
-- Viszont hasznos, mert rá szoktak kérdezni,
-- hogy mit jelent valami konkrét típusszignatúra.
-- Azért olyan feladatokat is rakok be,
-- ahol konkrét formális állításokat kell
-- emberi nyelven megfogalmazni.

module School
  (Person : Set)
  (_teaches_ : Person -> Person -> Set)
  (_friendsWith_ : Person -> Person -> Set)
  (_isIll : Person -> Set)
  (_sameAs_ : Person -> Person -> Set)
  where

  -- senki nem beteg
  AllHealthy : Set
  AllHealthy = {!!}

  -- valaki tanár (vagyis van valaki, akit tanít)
  _isTeacher : Person -> Set
  _isTeacher = {!!}

  -- valaki diák (vagyis van, aki tanítja)
  _isStudent : Person -> Set
  _isStudent = {!!}

  -- valaki tanár és diák egyszerre (nyugodtan használd az előzőket!)
  _isTeacherAndStudent : Person -> Set
  _isTeacherAndStudent = {!!}

  -- valaki diák, de van tanár barátja
  _isStudentWithTeacherFriend : Person -> Set
  _isStudentWithTeacherFriend = {!!}

  -- valakik kölcsönösen tanítják egymást
  _viceVersaWith_ : Person -> Person -> Set
  _viceVersaWith_ = {!!}

  -- valaki továbbképző (csak tanárokat tanít)
  _isTeacherOfTeachers : Person -> Set
  _isTeacherOfTeachers = {!!}

  -- ha mindenki magának a barátja
  -- akkor mindenkinek van barátja
  S1 : Set        -- kifogytam a nevekből...
  S1 = {!!}

  -- ha mindenkinek legalább egy tanára van,
  -- akkor mindenki azonos legalább egy barátjával
  -- (ez persze nem igaz, de azért formalizáld)
  S2 : Set
  S2 = {!!}

  -- ha valakinek pontosan egy tanára van,
  -- akkor ő a barátja is
  S3 : Set
  S3 = {!!}
