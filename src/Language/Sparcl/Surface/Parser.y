{
{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Surface.Parser where

import Language.Sparcl.Surface.Lexer
import Language.Sparcl.Surface.Syntax
import Language.Sparcl.Surface.ParserAux 

import Language.Sparcl.SrcLoc
import Language.Sparcl.Name
import Language.Sparcl.Literal
import Language.Sparcl.Pass
import Language.Sparcl.Multiplicity 

}

%tokentype { Loc Token }
%monad { Alex }
%lexer { lexer } { Loc _ Teof }
%error { parseError }

%name pExp    Exp 
%name pDecls  TopDecls
%name pModule Module  

%token
  "=" { Loc _ Tequal }
  ":" { Loc _ Tcolon }

  ";" { Loc _ Tsemi }
  "{" { Loc _ Tlbrace }
  "}" { Loc _ Trbrace }

  "," { Loc _ Tcomma }
  "(" { Loc _ Tlparen }
  ")" { Loc _ Trparen }

  lam  { Loc _ Tlam }
  "->" { Loc _ Trarrow }
  "."  { Loc _ Tdot }
  "forall" { Loc _ Tforall }
  "#"  { Loc _ Tsharp }
  "ω" { Loc _ Tomega } 

  "-o" { Loc _ Tlollipop }

  "!"  { Loc _ Tbang }

  "_"  { Loc _ Tunderscore } 

  "|"  { Loc _ Tbar } 

  "let"  { Loc _ Tlet }
  "in"   { Loc _ Tin }

  "case" { Loc _ Tcase }
  "of"   { Loc _ Tof }
  "with" { Loc _ Twith }
  "end"  { Loc _ Tend } 

  "data" { Loc _ Tdata }
  "type" { Loc _ Ttype } 
  
  "rev"  { Loc _ Trev }
  "fixity" { Loc _ Tfixity } 

  "lift"   { Loc _ Tlift }
  "unlift" { Loc _ Tunlift }
  "pin"    { Loc _ Tpin } 

  "def"    { Loc _ Tdef }
  "sig"    { Loc _ Tsig }

  "where"  { Loc _ Twhere } 


  "module" { Loc _ Tmodule } 
  "import" { Loc _ Timport } 

  -- {- a trick to allow 1/One/Omega/Many in the context where multiplicity is expected -}
  -- "1"     { Loc _ (Tintlit 1) } 
  -- "One"   { Loc _ (Tconid (User "One"))   }
  -- "Many"  { Loc _ (Tconid (User "Many"))  }
  -- "Omega" { Loc _ (Tconid (User "Omega")) } 

  -- {- a trick to allow "left" and "right" to occur as usual variables -}
  -- "left"   { Loc _ (Tvarid (User "left")) }
  -- "right"  { Loc _ (Tvarid (User "right")) } 

  op     { Loc _ (Top _) }
  qop    { Loc _ (Tqop _ _) }
  varid  { Loc _ (Tvarid _) }
  qvarid { Loc _ (Tqvarid _ _) }
  conid  { Loc _ (Tconid _) }
  qconid { Loc _ (Tqconid _ _) }

  char   { Loc _ (Tcharlit _) }
  int    { Loc _ (Tintlit _) } 
%%

-- Export lists and selective importing is not supported yet. 
Module :: { Module 'Parsing}
  : "module" ModuleName Exports "where" sequence(Import) TopDecls
       { Module $2 $3 $5 $6 }
  | sequence(Import) TopDecls
       { Module (ModuleName "Main") Nothing $1 $2 }

Exports :: { Maybe [Export 'Parsing] }
  : "(" sepEndBy(SurfaceName,",") ")" { Just $2 }
  |                                   { Nothing }

SurfaceName :: { Loc SurfaceName }
  : ConQName { $1 }
  | VarQName { $1 }

Import :: { Import 'Parsing }
  : "import" ModuleName ImportingNames { Import $2 $3 }

ImportingNames :: { Maybe [Loc SurfaceName] }
  : "(" sepEndBy(SurfaceName,",") ")" { Just $2 }
  |                                   { Nothing }

ModuleName :: { ModuleName }
  : ConQName {% toModuleName (location $1) (unLoc $1) }
  
Ty :: { Loc TyP }
  : "forall" sequence(VarName) "." Ty { foldr (\n r -> Loc (location n <> location r) $ TForall (unLoc n) r) $4 $2 }
  | AppTy "->" Ty  { Loc (location $1 <> location $3) $ TCon (BuiltIn nameTyArr) [noLoc $ TMult Omega, $1, $3] }
  | AppTy "-o" Ty  { Loc (location $1 <> location $3) $ TCon (BuiltIn nameTyArr) [noLoc $ TMult One,   $1, $3] }
  | AppTy "#" Multiplicity "->" Ty { Loc (location $1 <> location $3) $ TCon (BuiltIn nameTyArr) [$3, $1, $5] } 
  | AppTy          { $1 }

Multiplicity :: { Loc TyP }
  : VarName { fmap TVar $1 }
  | MConst  { fmap TMult $1 }

MConst :: { Loc Multiplicity }
  : int     {% case intTk (unLoc $1) of { 1 -> return $ Loc (location $1) One; n -> lexError $ show n ++ " is not a valid multiplicity" }}
  | "ω"    { Loc (location $1) Omega }
  | conid {% case unLoc $1 of
                 Tconid (User "One")   -> return $ Loc (location $1) One
                 Tconid (User "Many")  -> return $ Loc (location $1) Omega
                 Tconid (User "Omega") -> return $ Loc (location $1) Omega
                 Tconid c              -> lexError $ show c ++ " is not a valid multiplicity"}
                 

AppTy :: { Loc TyP }
  : ConQName nonEmptySequence(SimpleTy) { Loc (location $1 <> mconcat (map location $2)) $ TCon (unLoc $1) $2 }
  | "rev" SimpleTy { Loc (location $1 <> location $2) $
                     TCon (BuiltIn nameTyRev) [$2] }
  -- TODO: to be removed 
  | "!"   SimpleTy { Loc (location $1 <> location $2) $
                     TCon (BuiltIn nameTyBang) [$2] }
  | SimpleTy { $1 }

SimpleTy :: { Loc TyP }
  : ConQName { fmap (\c -> TCon c []) $1 }
  | VarName  { fmap TVar $1 }
  | TupleTy  { $1 }

TopDecls :: { DeclsP (Loc TopDeclP) }
  : sequence( TopDecl ) { Decls () $1 } 

TupleTy :: { Loc TyP }
  : "(" sepBy(Ty,",") ")" { mkTupleTy $2 } 

TopDecl :: { Loc TopDeclP }
  : LocalDecl
    { fmap DDecl $1 }
  | "data" ConName sequence(VarName) "=" sepBy1(CDecl,"|")
    { Loc (location $1 <> mconcat (map location $5)) $ DData (unLoc $2) (map unLoc $3) $5 }
  | "type" ConName sequence(VarName) "=" Ty
    { Loc (location $1 <> location $5) $ DType (unLoc $2) (map unLoc $3) $5 } 

CDecl :: { Loc CDeclP }
  : ConName sequence(SimpleTy)
    { Loc (location $1 <> mconcat (map location $2)) $ CDecl (unLoc $1) $2 } 
  
Assoc :: { Loc Assoc }
  : varid {% case unLoc $1 of
                Tvarid (User "left")  -> return $ L <$ $1
                Tvarid (User "right") -> return $ R <$ $1
                _                     -> lexError $ "associativity must be `left' or `right'" }
  |         { noLoc N } 

LocalDecls :: { DeclsP LDeclP }
  : sequence(LocalDecl) { Decls () $1 }
  
LocalDecl :: { LDeclP }
  : "def" VarOrOp sepBy1(Def, "|")
      { expandLoc $1 $ lddef (unLoc $2) $3 }
  | "sig" VarOrOp ":" Ty
      { expandLoc $1 $ Loc (location $4) $ DSig (unLoc $2) $4 }
  | "fixity" Op int Assoc
      { Loc (location $1 <> location $4) $ DFixity (unLoc $2) (Prec $ intTk $ unLoc $3) (unLoc $4) }

Def :: { ([LPatP], ClauseP) }
  : sequence(SimplePat) "=" Clause { ($1, $3) } 
  
Exp :: { Loc ExpP }
  : lam nonEmptySequence(SimplePat) "->" Exp
    { expandLoc $1 $ labs $2 $4 }
  | "let" LocalDecls "in" Exp
    { expandLoc $1 $ Loc (location $4) $ Let $2 $4 }
  | "case" Exp "of" Alts "end"  { expandLoc $1 $ lcase $2 $4 }
  | OpExp            { $1 }


OpExp :: { Loc ExpP }
  : OpExp QOp AppExp { lop $2 $1 $3 }
  | AppExp           { $1 } 

AppExp :: { Loc ExpP }
  : AppExp SimpleExp { lapp $1 $2 }
  | SimpleExp        { $1 }

SimpleExp :: { Loc ExpP }
  : QVarOrOp       { fmap Var $1 }
  | ConQName       { fmap (\c -> Con c) $1 }
  | "rev" ConQName { fmap (\c -> RCon c) $2 }
  | "lift"         { Loc (location $1) $ Lift }
  | "unlift"       { Loc (location $1) $ Unlift }
  | "pin"          { Loc (location $1) $ RPin }
  | Literal        { fmap Lit $1 }
  -- TODO: to be removed 
  | "!" SimpleExp  { expandLoc $1 $ Loc (location $2) (Bang $2) }
  | TupleExp       { $1 }

TupleExp :: { Loc ExpP }
  : "(" sepBy(Exp, ",") ")" { expandLoc $1 $ expandLoc $3 $ mkTupleExp $2 }
  | "rev" "(" sepBy(Exp, ",") ")" { expandLoc $1 $ expandLoc $4 $  mkTupleExpR $3 }

Literal :: { Loc Literal }
  : int  { fmap (LitInt . intTk) $1 }
  | char { fmap (LitChar . charTk) $1 }


Alts :: { [ (LPatP, ClauseP) ] }
  : MaybeBar sepBy(Alt,"|") {$2}

MaybeBar
  : "|" {} 
  |     {}

Alt :: { (LPatP, ClauseP) }
  : Pat "->" Clause { ($1, $3) } 


Clause :: { ClauseP }
  : Exp With Where { Clause $1 $3 $2 }

Where :: { DeclsP LDeclP }
  : "where" LocalDecls "end" { $2 } 
  |                          { Decls () [] }

With :: { Maybe LExpP }
  : "with" Exp { Just $2 }
  |            { Nothing } 

VarQName :: { Loc SurfaceName }
  : varid  { fmap qnameTk $1 }
  | qvarid { fmap qnameTk $1 }

ConQName :: { Loc SurfaceName }
  : conid  { fmap qnameTk $1 }
  | qconid { fmap qnameTk $1 }

QOp :: { Loc SurfaceName }
  : op  { fmap qnameTk $1 }
  | qop { fmap qnameTk $1 }

QVarOrOp :: { Loc SurfaceName }
  : "(" QOp ")" { $2 }
  | VarQName    { $1 } 

VarOrOp :: { Loc SurfaceName }
  : "(" Op ")" { $2 }
  | VarName    { $1 }

Op :: { Loc SurfaceName }
  : op { fmap qnameTk $1 }

VarName :: { Loc SurfaceName }
  : varid { fmap qnameTk $1 }

ConName :: { Loc SurfaceName }
  : conid { fmap qnameTk $1 }

Braces(e)
  : "{" e "}" { $2 } 

sepEndBy(e,sep)
  : e sep sepEndBy(e,sep) { $1 : $3 }
  | e                     { [$1] }
  |                       { [] } 

sepBy1(e,sep)
  : e sep sepBy1(e,sep) { $1 : $3 }
  | e                   { [$1] } 

sepBy(e, sep)
  : sepBy1(e, sep) { $1 }
  |                { [] } 
  
sequence(e)
  : e sequence(e) { $1 : $2 }
  |               { [] }

nonEmptySequence(e)
  : e sequence(e) { $1 : $2 } 

Pat :: { Loc PatP }
  : "rev" AppPat { expandLoc $1 $ Loc (location $2) $ PREV $2 }
  | AppPat { $1 }
  

AppPat :: { Loc PatP }
  : ConQName nonEmptySequence(SimplePat) { lpcon $1 $2 }
  | SimplePat                            { $1 }

SimplePat :: { Loc PatP }
  : ConQName { fmap (\c -> PCon c []) $1 }
  | VarName  { fmap PVar $1 }
  | "!" SimplePat   { expandLoc $1 $ Loc (location $2) $ PBang $2 } 
  | TuplePat        { $1 }
  | "_"      { Loc (location $1) (PWild ())} 

TuplePat :: { Loc PatP }
  : "(" sepBy(Pat,",") ")" { expandLoc $1 $ expandLoc $3 $ mkTuplePat $2 } 

{

lexer :: (Loc Token -> Alex b) -> Alex b
lexer k = alexMonadScan >>= k


  
}
