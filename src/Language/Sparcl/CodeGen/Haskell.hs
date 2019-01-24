{-# LANGUAGE NoMonomorphismRestriction #-}

module Language.Sparcl.CodeGen.Haskell where

import Data.Char (isLower, isUpper, isNumber, ord)

import Control.Monad.Cont hiding (lift) 
import Control.Monad.State hiding (lift)

import qualified Control.Monad.Trans as T (lift) 

import Language.Sparcl.Name
import Language.Sparcl.Literal

import Language.Sparcl.Pretty hiding ((<$>))
import Language.Sparcl.Core.Syntax as C

import Prelude hiding (abs)

class NameGen m n where
  newName :: m n

class IsName n where
  fromName :: Name -> n 

instance IsName Name where
  fromName = id
  
class (Monad m, IsName n, NameGen m n, MiniHaskellPat n p) =>
      MiniHaskellExp m n p e d | e -> p, e -> n, e -> d, d -> e where
  var :: n -> m e 
  lit :: Literal -> m e 
  app :: e -> e -> m e
  abs :: n -> e -> m e

  con :: n -> [e] -> m e
  case_ :: e -> [(p, e)] -> m e

  let_ :: d -> e -> m e
  bind :: [(n, e)] -> m d 

  lift   :: e -> e -> m e
  unlift :: e -> m e

  rcase :: e -> [(e,e, e,e)] -> m e
  rpin  :: e -> e -> m e
  rpair :: e -> e -> m e 
  runit :: m e 

  rununit :: e -> e -> m e 
  runpair :: e -> e -> m e 

  just :: e -> m e -- Just in Haskell
  nothing :: m e   -- Nothing in Haskell 

class IsName n => MiniHaskellPat n p | p -> n where
  pvar :: n -> p
  pcon :: n -> [p] -> p 
  
  
modulePrefix :: String
modulePrefix = "Sparcl"

runtimePrefix :: String
runtimePrefix = "Language.Sparcl.Runtime."

baseSubstitute :: String
baseSubstitute = "Language.Sparcl.Base"

rhsName :: Name -> String
rhsName nn@(Original (ModuleName m) n _)
  | nn == conTrue  = "Prelude.True"
  | nn == conFalse = "Prelude.False"
  | ModuleName m == baseModule =
    let s = unUser n
    in parensIfs (isOp s) $ baseSubstitute ++ "." ++ encNameG s 
  | otherwise =
    let s = unUser n
    in parensIfs (isOp s) $ modulePrefix ++ "." ++ m ++ "." ++ encNameG s

rhsName (Alpha i n)      = "_a" ++ encNameL (unUser n) ++ show i
rhsName (Local n)        = "_l" ++ encNameL (unUser n)
rhsName (Generated n p)  = "_g" ++ phaseStr p ++ show n

parensIfs :: Bool -> String -> String
parensIfs True s = "(" ++ s ++ ")"
parensIfs False s = s 


lhsName :: Name -> String
lhsName (Original _ n _) =
  let s = unUser n
  in parensIfs (isOp s) $ encNameG s
lhsName (Alpha i n)      = "_a" ++ encNameL (unUser n) ++ show i
lhsName (Local n)        = "_l" ++ encNameL (unUser n)
lhsName (Generated n p)  = "_g" ++ phaseStr p ++ show n 

phaseStr :: Phase -> String
phaseStr Desugaring = "d"
phaseStr CodeGen    = "c"

encNameL :: String -> String
encNameL = go
  where
    go [] = []
    go (c:cs)
      | c == 'z' = "zz" ++ go cs
      | c == '_' = "z_" ++ go cs
      | isLower c || isUpper c || isNumber c = c:go cs
      | otherwise = "z" ++ (show $ ord c) ++ go cs 

isOp :: String -> Bool
isOp s
  | h:_ <- s, isLower h = False
  | h:_ <- s, isUpper h = False
  | otherwise           = True 

encNameG :: String -> String
encNameG n = n

unUser :: NameBase -> String
unUser (User n) = n 
unUser _        = error "Expected user-defined name."

newtype NameSource = NameSource Int
  deriving (Enum, Show, Eq, Ord)

newNameState :: State Int Name
newNameState = do
  i <- get
  put $! i+1
  return $ Generated i CodeGen 

pprCont :: Bool -> (Doc -> State Int Doc) -> Doc -> State Int Doc
pprCont isPure k body = do 
  x <- newNameState
  d <- k (text $ rhsName x)
  return $ vcat [mkSubst isPure x body, d]
  where
    mkSubst True  x b = hsep [text "let", text $ lhsName x, text "=", align b]
    mkSubst False x b = hsep [text $ lhsName x, text "<-", align b]
     
pprDo :: ContT Doc (State Int) Doc -> State Int Doc
pprDo m = do
  doc <- runContT m (\v -> return $ hsep [ text "return", v ])
  return $ text "do" <+> align doc
--  text "do" <+> align (runCont m (\e ns' _ -> hsep [text "return", e ns' 10]) ns 0)
                       

instance MiniHaskellPat Name (Precedence -> Doc) where
  pvar n = \_ -> text (lhsName n)
  pcon n ps = \prec ->
    case n of
      (Original _ (System (NTuple _)) _) ->
        parens $ hsep (punctuate comma $ map (\p -> p 0) ps)
      _ ->
        parensIf (prec > 0) $ hsep (text (rhsName n) : map (\p -> p 1) ps)

type TextGen = Precedence -> Doc

instance NameGen (State Int) Name where
  newName = newNameState

instance NameGen (ContT r (State Int)) Name where
  newName = T.lift newNameState 


addReturn :: Cont Doc Doc -> Doc
addReturn e = runCont e $ \d -> text "return" <+> d 

addLet :: Name -> Doc -> (Doc -> Doc) -> Doc
addLet x d k =
  vcat [ hsep [text "let", text (lhsName x), text "=", align d],
         k (text $ rhsName x) ]

addBind :: Name -> Doc -> (Doc -> Doc) -> Doc
addBind x d k =
  vcat [ hsep [ text (lhsName x), text "<-", align d],
         k (text $ rhsName x) ]

instance MiniHaskellExp (State Int) Name
                        (Precedence -> Doc) (Cont Doc Doc) Doc where
  var n = return $ return $ text (rhsName n)
  lit n = return $ return $ text (prettyShow n)
  
  app e1 e2 = do
    r <- newName
    return $ cont $ \k -> do
      runCont e1 $ \d1 ->
        runCont e2 $ \d2 ->
         addBind r (d1 <+> d2) k 
                         
  abs x e = do
    r <- newName 
    return $ cont $ \k ->
      let body = hcat [ text "\\", text (lhsName x)] <+> text "->" <+> text "do" 
                 <> nest 2 (line <> addReturn e)
      in addLet r body k 
            

--     ContT $ \k -> do
-- --    d <- pprDo e 
--     let body = hcat[ text "\\", text (lhsName x) ] <+> text "->" <>
--                nest 2 (line <> e)
--     pprCont True k body

{-
  con n [e1, e2] = do
    r <- newName
    return $ cont $ \k ->
      runCont e1 $ \d1 ->
        runCont e2 $ \d2 ->
          vcat [ [d1,d2], 
  
-}

  con n _es = do
    r <- newName
    return $ cont $ \k -> go r [] _es k
      -- foldl (\kk e -> runCont e $ \d -> kk . ((d <> sep) <+>))
      --       (\d -> vcat [ hsep [ text "let", text (lhsName r), text "=", align $ enc d ],
      --                     k (text (rhsName r))])
      --    es (text "")
    where
      go r ds [] k = addLet r (align $ makeCon $ reverse ds) k 
      go r ds (e:es) k =
        runCont e $ \d -> go r (d:ds) es k 
      
      makeCon ds = 
          case n of
            (Original _ (System (NTuple _)) _) ->
              parens $ hsep $ punctuate comma ds 
            _ ->
              text (rhsName n) <+> hsep ds 
    

  case_ e0 pes = do
    r <- newName 
--    dpes <- mapM (\(p,e) -> fmap (\d -> p 0 <+> text "->" <+> nest 2 (line <> d)) $ pprDo e) pes
    let dpes = map (\(p,e) -> p 0 <+> text "->" <+> text "do" <+> nest 2 (line <> align (addReturn e))) pes
    return $ cont $ \k -> 
      runCont e0 $ \d0 -> 
                     let body = nest 2 $ 
                           hsep [text "case", align d0, text "of"] <> 
                           line <> vcat dpes
                     in addBind r body k 
                      

  bind ds = 
    return $ vcat $ map (\(n,e) -> align $ hsep [text (lhsName n), text "=",
                                                 text (runtimePrefix ++ "runRevUnsafe"), text "Prelude.$",
                                                 text "do", nest 2 $ line <> addReturn e]) ds


  let_ dbind e1 = return $ cont $ \k -> 
    let out = text "let" <+> align dbind
    in out <> line <>
        (runCont e1 $ \d1 -> k d1)

  lift e1 e2 = do
    r <- newName
    return $ cont $ \k ->
      runCont e1 $ \d1 ->
      runCont e2 $ \d2 ->
      addBind r (hsep [ text (runtimePrefix ++ "liftRev"), d1 , d2 ]) k 


  unlift e = do
    r <- newName
    return $ cont $ \k ->
      runCont e $ \d ->
      addBind r (hsep [ text (runtimePrefix ++ "unliftRev"), d]) k 


  
  rcase e0 e4s = do
    r <- newName
    i <- newName
    return $ cont $ \k ->
      runCont e0 $ \d0 ->
        go r i d0 [] e4s k 
    where
      go r _ d0 ds [] k =
        addBind r (hsep [ text (runtimePrefix ++ "caseRev"), d0]
                   <> nest 2 (line <> (brackets $ align $ vcat $ punctuate comma $ reverse ds))) k
      go r i d0 ds ((e1,e2,e3,e4):rest) k =
        runCont e1 $ \d1 ->
        runCont e2 $ \d2 ->
        runCont e4 $ \d4 ->
        let d3 = text "\\" <> text (lhsName i) <+> text "->" <+> text "do" <>
                 nest 2 (line <> runCont e3 (\f -> parens (f <+> text (rhsName i))))
        in go r i d0 (hsep [text (runtimePrefix ++ "Branch"), d1,d2,parens d3,d4]:ds) rest k
       
  rpin e1 e2 = do
    r <- newName
    return $ cont $ \k ->
      runCont e1 $ \d1 ->
      runCont e2 $ \d2 -> 
      addBind r (hsep [ text $ runtimePrefix ++ "pinRev", d1, d2 ]) k

  rpair e1 e2 = do
    r <- newName
    return $ cont $ \k -> 
      runCont e1 $ \d1 ->
      runCont e2 $ \d2 ->
      addBind r (hsep [ text $ runtimePrefix ++ "pairRev", d1, d2 ]) k

  runit = do
    r <- newName 
    return $ cont $ \k ->
      addBind r (text (runtimePrefix ++ "unitRev")) k 


  just e = do
    r <- newName
    return $ cont $ \k ->
      runCont e $ \d -> 
      addLet r (hsep [ text "Prelude.Just", d]) k 

  nothing = do
    return $ cont $ \k ->
      k (text "Prelude.Nothing")

  rununit e1 e2 = do
    r <- newName 
--    d <- pprDo m
    return $ cont $ \k ->
      runCont e1 $ \d1-> 
      let body = hsep [ text $ runtimePrefix ++ "ununitRev", d1, text "Prelude.$", text "do" ]
                 <> nest 2 (line <> align (addReturn e2))
      in addBind r body k 

  runpair e1 e2 = do
    r  <- newName
    rr <- newName
    rrr <- newName 
    x <- newName
    y <- newName
--    d <- pprDo m
    return $ cont $ \k ->
      runCont e1 $ \d1 ->
      let body2 = text "\\" <> text (lhsName x) <+> text (lhsName y) <+> text "->" <+> text "do"
                  <> nest 2 (line <> (runCont e2 $ \d2 ->
                                         addBind rr (d2 <+> text (rhsName x)) $ \d3 ->
                                         addBind rrr (d3 <+> text (rhsName y)) $ \d -> hsep [ text "return", d ]))
          body = hsep [ text $ runtimePrefix ++ "unpairRev", d1, text "Prelude.$" ]
                 <> nest 2 (line <> align body2)
      in addBind r body k 

toDocExp :: (forall m n p e d. MiniHaskellExp m n p e d => m e) -> Doc
toDocExp (m :: State Int (Cont Doc Doc)) = runCont (evalState m 0) id
  -- where
  --   toDocExpImpl :: ContT Doc (State Int) Doc -> Doc
  --   toDocExpImpl m = evalState (runContT m return) 0 

toDocDec :: (forall m n p e d. MiniHaskellExp m n p e d => m d) -> Doc
toDocDec (m :: State Int Doc) = evalState m 0 

genBind :: MiniHaskellExp m n p e d => C.Bind Name -> m d 
genBind ds = do
  ds' <- mapM (\(x,e) -> do
                  e' <- genExp e
                  return (fromName x, e')) ds
  bind ds'

genExp :: MiniHaskellExp m n p e d => C.Exp Name -> m e
genExp (C.Var x) = var (fromName x)
genExp (C.Lit l) = lit l
genExp (C.App e1 e2) = do 
  x <- genExp e1
  y <- genExp e2
  app x y
genExp (C.Abs x e) = 
  abs (fromName x) =<< genExp e
genExp (C.Con n es) = do
  xs <- mapM genExp es
  con (fromName n) xs
genExp (C.Bang e) = genExp e
genExp (C.Case e0 pes) = do
  x <- genExp e0
  pes' <- mapM (\(p,e) -> do
                   e' <- genExp e
                   return (genPat p, e')) pes
  case_ x pes' 
genExp (C.Let ds e1) = do
  ds' <- genBind ds
  x <- genExp e1
  let_ ds' x
genExp (C.Lift e1 e2) = do
  x <- genExp e1
  y <- genExp e2
  lift x y
genExp (C.Unlift e) = do
  x <- genExp e
  unlift x
  
genExp (C.RPin e1 e2) = do
  x <- genExp e1
  f <- genExp e2
  rpin x f
 
genExp (C.RCon n es) = do
  let len = length es
  x <- newName
  zs <- mapM (const newName) [1..len]
  es' <- mapM genExp es
  e'  <- pairsToRightR es'
  let n' = fromName n 
  vx <- var x 
  fwd <- do
    body <- con n' =<< mapM var zs
    abs x =<< case_ vx [ (pairsToRightP (map pvar zs), body) ]

  bwd <- do
    body <- pairsToRight =<< mapM var zs
    abs x =<< case_ vx [ (pcon n' (map pvar zs), body) ]

  f <- lift fwd bwd
  app f e' 

genExp (C.RCase e0 alts) = do
  e0' <- genExp e0
  alts' <- mapM genRAlts alts
  rcase e0' alts'


genRAlts :: MiniHaskellExp m n p e d => (Pat Name, Exp Name, Exp Name) -> m (e, e, e, e)
genRAlts (pat, bexp, wexp) = do
  x <- newName 
  vx <- var x
  let fvP  = map fromName $ freeVarsP pat 
  let pat' = genPat pat
  -- let just x  = con (Original (ModuleName "Prelude") (User "Just"))   [x]
  -- let nothing = con (Original (ModuleName "Prelude") (User "Nothing")) []
  
  f <- do
    body1 <- just =<< pairsToRight =<< mapM var fvP
    body2 <- nothing 
    abs x =<< case_ vx [ (pat', body1), (pvar x, body2) ]
  g <- do
    body1 <- just =<< genExpFromPat pat
    abs x =<< case_ vx [ (pairsToRightP (map pvar fvP), body1) ]

  wexp' <- genExp wexp

  bexp' <- do    
        abs x =<< mkUnpairs x fvP =<< genExp bexp
  return (f, g, bexp', wexp') 
  where
    mkUnpairs x [] body = do
      vx <- var x
      rununit vx body 
    mkUnpairs x [y] body = do 
      f <- abs y body
      z <- var x
      app f z 
    mkUnpairs x (y:ys) body = do
      vx <- var x
      r <- newName 
      runpair vx =<< (abs y =<< abs r =<< mkUnpairs r ys body)
  
  
  


mkTup :: MiniHaskellExp m n p e d => [e] -> m e
mkTup [e] = return e
mkTup es  = con (fromName $ nameTuple $ length es) es            
                                              
genPat :: MiniHaskellPat n p => C.Pat Name -> p
genPat (C.PVar x) = pvar (fromName x)
genPat (C.PBang p) = genPat p
genPat (C.PCon n ps) = pcon (fromName n) (map genPat ps)

genExpFromPat :: MiniHaskellExp m n p e d => C.Pat Name -> m e
genExpFromPat (C.PVar x) = var (fromName x)
genExpFromPat (C.PBang p) = genExpFromPat p
genExpFromPat (C.PCon n ps) = con (fromName n) =<< mapM genExpFromPat ps 

pairsToRight :: MiniHaskellExp m n p e d => [e] -> m e
pairsToRight []  = mkTup []
pairsToRight [e] = return e
pairsToRight (e:es) = do
  r' <- pairsToRight es
  mkTup [e, r']


pairsToRightR :: MiniHaskellExp m n p e d => [e] -> m e
pairsToRightR []  = runit
pairsToRightR [e] = return e
pairsToRightR (e:es) = do
  r' <- pairsToRightR es
  rpair e r'

pairsToRightP :: MiniHaskellPat n p => [p] -> p
pairsToRightP []  = pcon (fromName $ nameTuple 0) []
pairsToRightP [p] = p
pairsToRightP (p:ps) =
  pcon (fromName $ nameTuple 2) [p, pairsToRightP ps]
