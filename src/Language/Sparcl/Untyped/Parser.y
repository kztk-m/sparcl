{
{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Untyped.Parser where

import Language.Sparcl.Untyped.Lexer
import Language.Sparcl.Untyped.Syntax
import Language.Sparcl.Untyped.ParserAux 

import Language.Sparcl.SrcLoc
import Language.Sparcl.Name
import Language.Sparcl.Literal
  
}

%tokentype { Loc Token }
%monad { Alex }
%lexer { lexer } { Loc _ TkEOF }
%error { parseError }

%name pExp    Exp 
%name pDecls  TopDecls
%name pModule Module  

%token
  "=" { Loc _ (TkPunct "=") }
  ":" { Loc _ (TkPunct ":") }

  ";" { Loc _ (TkPunct ";") }
  "{" { Loc _ (TkPunct "{") }
  "}" { Loc _ (TkPunct "}") }

  "," { Loc _ (TkPunct ",") }
  "(" { Loc _ (TkPunct "(") }
  ")" { Loc _ (TkPunct ")") }

  "\\" { Loc _ (TkPunct "\\") }
  "->" { Loc _ (TkPunct "->") }
  "."  { Loc _ (TkPunct ".") }
  "forall" { Loc _ (TkPunct "forall") }

  "!"  { Loc _ (TkPunct "!") }

  "_"  { Loc _ (TkPunct "_") } 

  "|"  { Loc _ (TkPunct "|") } 

  "let"  { Loc _ (TkKey "let") }
  "in"   { Loc _ (TkKey "in") }

  "case" { Loc _ (TkKey "case") }
  "of"   { Loc _ (TkKey "of") }
  "with" { Loc _ (TkKey "with") }
  "end"  { Loc _ (TkKey "end") } 
  
  "rev"  { Loc _ (TkKey "rev") }
  "fixity" { Loc _ (TkKey "fixity") } 
  "forward"  { Loc _ (TkKey "forward") }
  "backward" { Loc _ (TkKey "backward") }

  "lift"   { Loc _ (TkKey "lift") }
  "unlift" { Loc _ (TkKey "unlift") }

  "def"    { Loc _ (TkKey "def") }
  "sig"    { Loc _ (TkKey "sig") }

  "where"  { Loc _ (TkKey "where") } 


  "module" { Loc _ (TkKey "module") } 
  "import" { Loc _ (TkKey "import") } 

  "left"   { Loc _ (TkVarID (NormalName "left")) }
  "right"  { Loc _ (TkVarID (NormalName "right")) } 

  op     { Loc _ (TkOp _) } 
  char   { Loc _ (TkCharLit _) }
  varId  { Loc _ (TkVarID _) }
  qVarId { Loc _ (TkQVarID _) }
  conId  { Loc _ (TkConID _) }
  int    { Loc _ (TkIntLit _) } 

%%

-- Export lists and selective importing is not supported yet. 
Module :: { Module }
  : "module" ModuleName Exports "where" sequence(Import) TopDecls
       { Module $2 $3 $5 $6 }
  | sequence(Import) TopDecls
       { Module ["Main"] [] $1 $2 }

Exports :: { [Export] }
  : "(" sepEndBy(QName,",") ")" { $2 }
  |                             { [] }

QName :: { QName }
  : ConQName { unLoc $1 }
  | VarQName { unLoc $1 }

Import :: { Import }
  : "import" ModuleName ImportingNames { Import $2 $3 }

ImportingNames :: { Maybe [QName] }
  : "(" sepEndBy(QName,",") ")" { Just $2 }
  |                             { Nothing }

ModuleName :: { ModuleName }
  : ConQName {% toModuleName (location $1) (unLoc $1) }
  
Ty :: { Loc Ty }
  : "forall" sequence(VarName) "." Ty { foldr (\n r -> Loc (location n <> location r) $ TForall (unLoc n) r) $4 $2 }
  | AppTy "->" Ty  { Loc (location $1 <> location $3) $ TCon nameTyArr [$1, $3] }
  | AppTy          { $1 }

AppTy :: { Loc Ty }
  : ConQName nonEmptySequence(SimpleTy) { Loc (location $1 <> mconcat (map location $2)) $ TCon (unLoc $1) $2 }
  | "rev" SimpleTy { Loc (location $1 <> location $2) $
                     TCon nameTyRev [$2] }
  | "!"   SimpleTy { Loc (location $1 <> location $2) $
                     TCon nameTyBang [$2] }
  | SimpleTy { $1 }

SimpleTy :: { Loc Ty }
  : ConQName { fmap (\c -> TCon c []) $1 }
  | VarName  { fmap TVar $1 }
  | TupleTy  { $1 }

TopDecls :: { [LDecl] }
  : sequence( TopDecl ) { $1 } 

TupleTy :: { Loc Ty }
  : "(" sepBy(Ty,",") ")" { mkTupleTy $2 } 

TopDecl :: { LDecl }
  : LocalDecl { $1 }
  | "fixity" BareOp int Assoc { Loc (location $1 <> location $4) $ DFixity (unLoc $2) (Prec $ intTk $ unLoc $3) (unLoc $4) }

Assoc :: { Loc Assoc }
  : "left"  { L <$ $1 }
  | "right" { R <$ $1 }
  |         { noLoc N } 
  
LocalDecl :: { LDecl }
  : "def" VarName sepBy1(Def, "|") { expandLoc $1 $ lddef (unLoc $2) $3 }
  | "sig" VarName ":" Ty               { expandLoc $1 $ Loc (location $4) $ DSig (unLoc $2) $4 }

Def :: { ([LPat], Clause) }
  : sequence(SimplePat) "=" Clause { ($1, $3) } 
  
Exp :: { Loc Exp }
  : "\\" nonEmptySequence(SimplePat) "->" Exp
    { expandLoc $1 $ labs $2 $4 }
  | "let" sequence(LocalDecl) "in" Exp
    { expandLoc $1 $ Loc (location $4) $ Let $2 $4 }
  | "case" Exp "of" Alts "end"  { expandLoc $1 $ lcase $2 $4 }
  | OpExp            { $1 }


OpExp :: { Loc Exp }
  : OpExp op AppExp { expandLoc $2 $ lop (fmap qnameTk $2) $1 $3 }
  | AppExp          { $1 } 

AppExp :: { Loc Exp }
  : AppExp SimpleExp { lapp $1 $2 }
  | "lift" SimpleExp SimpleExp { expandLoc $1 $ Loc (location $2 <> location $3) $ Lift $2 $3 }
  | "unlift" SimpleExp         { expandLoc $1 $ Loc (location $2) $ Unlift $2 }
  | "forward" SimpleExp        { expandLoc $1 $ Loc (location $2) $ Fwd $2 }
  | "backward" SimpleExp       { expandLoc $1 $ Loc (location $2) $ Bwd $2 } 
  | SimpleExp        { $1 }

SimpleExp :: { Loc Exp }
  : VarQName   { fmap Var $1 }
  | ConQName   { fmap (\c -> Con c []) $1 }
  | "rev" ConQName { fmap (\c -> RCon c []) $2 }
  | Literal  { fmap Lit $1 } 
  | "!" SimpleExp { expandLoc $1 $ Loc (location $2) (Bang $2) }
  | TupleExp      { $1 }

TupleExp :: { Loc Exp }
  : "(" sepBy(Exp, ",") ")" { expandLoc $1 $ expandLoc $3 $ mkTupleExp $2 }

Literal :: { Loc Literal }
  : int  { fmap (LitInt . intTk) $1 }
  | char { fmap (LitChar . charTk) $1 }


Alts :: { [ (LPat, Clause) ] }
  : MaybeBar sepBy(Alt,"|") {$2}

MaybeBar
  : "|" {} 
  |     {}

Alt :: { (LPat, Clause) }
  : Pat "->" Clause { ($1, $3) } 


Clause :: { Clause }
  : Exp With Where { Clause $1 $3 $2 }

Where :: { [LDecl] }
  : "where" sequence( LocalDecl ) "end" { $2 } 
  |                                     { [] }

With :: { Maybe LExp }
  : "with" Exp { Just $2 }
  |            { Nothing } 

VarQName :: { Loc QName }
  : varId  { fmap qnameTk $1 }
  | qVarId { fmap qnameTk $1 }

ConQName :: { Loc QName }
  : conId  { fmap qnameTk $1 } 

BareOp :: { Loc Name }
  : op {% traverse (unquantify . qnameTk) $1 }             

VarName :: { Loc Name }
  : varId { fmap nameTk $1 } 

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

Pat :: { Loc Pat }
  : "rev" AppPat { expandLoc $1 $ Loc (location $2) $ PREV $2 }
  | AppPat { $1 }
  

AppPat :: { Loc Pat }
  : ConQName nonEmptySequence(SimplePat) { lpcon $1 $2 }
  | SimplePat                            { $1 }

SimplePat :: { Loc Pat }
  : ConQName { fmap (\c -> PCon c []) $1 }
  | VarName  { fmap PVar $1 }
  | "!" SimplePat   { expandLoc $1 $ Loc (location $2) $ PBang $2 } 
  | TuplePat        { $1 }
  | "_"      { Loc (location $1) PWild } 

TuplePat :: { Loc Pat }
  : "(" sepBy(Pat,",") ")" { expandLoc $1 $ expandLoc $3 $ mkTuplePat $2 } 

{

lexer :: (Loc Token -> Alex b) -> Alex b
lexer k = alexMonadScan >>= k


  
}
