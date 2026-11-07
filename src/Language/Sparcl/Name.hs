module Language.Sparcl.Name where

import Control.DeepSeq
import Language.Sparcl.Pretty as D

data NameBase
  = User !String
  | System !SystemName
  deriving (Eq, Ord, Show)

instance NFData NameBase where
  rnf (User n) = rnf n
  rnf (System _) = ()

instance Pretty NameBase where
  ppr (User n) = text n
  ppr (System s) = ppr s

data SystemName
  = -- | name for n-tuple constructor/type
    NTuple !Int
  | -- | name for n-additive product constructor/type
    NWTuple !Int
  | -- | name for an arrow kind
    KArrow
  | -- | name for function types (ternary)
    NArrow
  | -- | name for instance-argument function types (binary, always unrestricted)
    NInstArrow
  | -- | name for unrestricted type constructor (to be removed)
    NBang
  | -- | name for invertible type constructor
    NRev
  | -- | generated name for an unnamed instance (numbered within a module)
    NInstance !Int
  | -- | dictionary constructor of a class (the class's base name); used
    --   with the module declaring the class
    NDict !NameBase
  | -- | projection of the i-th superclass dictionary of a class (the
    --   class's base name); used with the module declaring the class
    NSuperProj !NameBase !Int
  | -- | default implementation of a method (the method's base name); used
    --   with the module declaring the class
    NDefault !NameBase
  deriving (Eq, Ord, Show)

instance Pretty SystemName where
  ppr (NTuple n) = text "<Tup" <+> ppr n <> text ">"
  ppr (NWTuple n) = text "<&Tup" <+> ppr n <> text ">"
  ppr NArrow = text "->" -- NB: ternary (Multiplicity -> Type -> Type -> Type) instead of binary
  ppr NInstArrow = text "{{->}}" -- NB: binary (Type -> Type -> Type)
  ppr KArrow = text "->"
  ppr NBang = text "!" -- TODO: will be removed
  ppr NRev = text "rev"
  ppr (NInstance k) = text "<instance #" <> ppr k <> text ">"
  ppr (NDict c) = text "<dict" <+> ppr c <> text ">"
  ppr (NSuperProj c i) = text "<super" <+> ppr c <+> text "#" <> ppr i <> text ">"
  ppr (NDefault m) = text "<default" <+> ppr m <> text ">"

data SurfaceName
  = Qual !ModuleName !NameBase
  | Bare !NameBase
  | BuiltIn !Name -- for built-in things
  deriving (Eq, Ord, Show)

data Name
  = Local !NameBase
  | Original !ModuleName !NameBase !SurfaceName
  | Alpha !Int !NameBase
  | Generated !Int !Phase
  deriving Show

data Phase = Desugaring | REPL | TypeChecking deriving (Eq, Show, Ord)

instance NFData Phase where
  rnf x = seq x ()

instance Eq Name where
  Local n1 == Local n2 = n1 == n2
  Original m1 n1 _ == Original m2 n2 _ = m1 == m2 && n1 == n2
  Alpha i1 _ == Alpha i2 _ = i1 == i2
  Generated i1 p1 == Generated i2 p2 = i1 == i2 && (p1 == p2)
  _ == _ = False

instance Ord Name where
  compare (Local n1) (Local n2) = compare n1 n2
  compare (Local _) _ = LT
  compare (Original _ _ _) (Local _) = GT
  compare (Original m1 n1 _) (Original m2 n2 _) = compare (m1, n1) (m2, n2)
  compare (Original _ _ _) _ = LT
  compare (Alpha _ _) (Generated _ _) = LT
  compare (Alpha i1 _) (Alpha i2 _) = compare i1 i2
  compare (Alpha _ _) _ = GT
  compare (Generated i1 p1) (Generated i2 p2) = compare (p1, i1) (p2, i2)
  compare (Generated _ _) _ = GT

instance NFData SurfaceName where
  rnf (Qual m n) = rnf (m, n)
  rnf (Bare n) = rnf n
  rnf (BuiltIn n) = rnf n

instance NFData Name where
  rnf (Local n) = rnf n
  rnf (Original m n orig) = rnf (m, n, orig)
  rnf (Alpha _ n) = rnf n
  rnf (Generated _ p) = rnf p

newtype ModuleName = ModuleName String
  deriving (Show, Eq, Ord, NFData)

instance Pretty ModuleName where
  ppr (ModuleName m) = text m

instance Pretty SurfaceName where
  ppr (Qual m n) = ppr m <> text "." <> ppr n
  ppr (Bare n) = ppr n
  ppr (BuiltIn n) = ppr n

-- Basically, the method pretty-print names as the original without additional
-- information introduced in the system.
instance Pretty Name where
  ppr (Generated i p) = text "_" <> text (case p of Desugaring -> "d"; REPL -> "r"; TypeChecking -> "t") <> ppr i
  ppr (Alpha _i n) = ppr n
  ppr (Local n) = ppr n
  ppr (Original _ _ o) = ppr o

moduleNameToStr :: ModuleName -> String
moduleNameToStr (ModuleName ms) = ms

-- Names generated for type classes (H-4-3 1). Each is an 'Original' name in
-- the module declaring the class (or the method), so that expressions built
-- in other modules refer to the same names.

-- | A 'System' name made from the base of a top-level name, in its module.
systemNameAt :: String -> (NameBase -> SystemName) -> Name -> Name
systemNameAt _ f (Original m base _) = let s = System (f base) in Original m s (Bare s)
systemNameAt what _ n = error $ "Cannot happen: " ++ what ++ " must be a top-level name: " ++ show n

-- | The dictionary constructor of a class (H-4-2).
dictName :: Name -> Name
dictName = systemNameAt "a class" NDict

-- | The projection of the i-th superclass dictionary of a class (E-3).
superProjName :: Name -> Int -> Name
superProjName c i = systemNameAt "a class" (`NSuperProj` i) c

-- | The default implementation of a method (G-5 2).
defaultName :: Name -> Name
defaultName = systemNameAt "a method" NDefault

isDictName :: Name -> Bool
isDictName (Original _ (System (NDict _)) _) = True
isDictName _ = False

isSuperProjName :: Name -> Bool
isSuperProjName (Original _ (System (NSuperProj _ _)) _) = True
isSuperProjName _ = False

isDefaultName :: Name -> Bool
isDefaultName (Original _ (System (NDefault _)) _) = True
isDefaultName _ = False

-- data QName = QName ModuleName Name -- qualified name (for global names)
--            | BName Name            -- bare name
--            deriving (Show, Eq, Ord)

-- instance NFData QName where
--   rnf (QName m n) = rnf (m, n)
--   rnf (BName n)   = rnf n

-- instance Pretty QName where
--   ppr (QName m n) =
--     (case n of
--         Generated _ -> id
--         NormalName (c:_) | isLower c || isUpper c -> id
--         _                            -> D.parens) $
--     D.text (moduleNameToStr m) D.<> D.text "." D.<> ppr n
--   ppr (BName n)   = ppr n

baseModule :: ModuleName
baseModule = ModuleName "Base"

nameInBase :: NameBase -> Name
nameInBase bn = Original baseModule bn (Qual baseModule bn)

conTrue :: Name
conTrue = nameInBase (User "True")

conFalse :: Name
conFalse = nameInBase (User "False")

nameTuple :: Int -> Name
nameTuple n =
  let bn = System (NTuple n)
  in  Original baseModule bn (Bare bn)

nameWTuple :: Int -> Name
nameWTuple n =
  let bn = System (NWTuple n)
  in  Original baseModule bn (Bare bn)

class NameCheck n where
  checkNameTuple :: n -> Maybe Int
  checkNameTyTuple :: n -> Maybe Int

  checkNameWTuple :: n -> Maybe Int
  checkNameTyWTuple :: n -> Maybe Int

instance NameCheck Name where
  checkNameTuple (Original _ (System (NTuple m)) _) = Just m
  checkNameTuple _ = Nothing

  checkNameTyTuple = checkNameTuple

  checkNameWTuple = checkNameTyWTuple

  checkNameTyWTuple (Original _ (System (NWTuple m)) _) = Just m
  checkNameTyWTuple _ = Nothing

nameUnit :: Name
nameUnit = nameTuple 0

nameTyTuple :: Int -> Name
nameTyTuple = nameTuple

nameTyWTuple :: Int -> Name
nameTyWTuple = nameWTuple

nameTyBang :: Name
nameTyBang = nameInBase (System NBang)

nameTyRev :: Name
nameTyRev = nameInBase (System NRev)

nameTyInt :: Name
nameTyInt = nameInBase (User "Int")

nameTyDouble :: Name
nameTyDouble = nameInBase (User "Double")

nameTyChar :: Name
nameTyChar = nameInBase (User "Char")

nameTyBool :: Name
nameTyBool = nameInBase (User "Bool")

nameTyRational :: Name
nameTyRational = nameInBase (User "Rational")

nameTyList :: Name
nameTyList = nameInBase (User "List")

-- nameTyLArr :: Name
-- nameTyLArr = nameInBase (System NLinearArrow)

nameTyArr :: Name
nameTyArr = nameInBase (System NArrow)

nameTyInstArr :: Name
nameTyInstArr = nameInBase (System NInstArrow)

nameKiArr :: Name
nameKiArr = nameInBase (System KArrow)

nameKindType :: Name
nameKindType = nameInBase (User "Type")

nameKindMultiplicity :: Name
nameKindMultiplicity = nameInBase (User "Multiplicity")
