module Language.Sparcl.Command where

import qualified Data.Map               as M
import           Language.Sparcl.Pretty as D

import           Control.Arrow          (first)
import           Data.Char              (isSpace)
import           Data.Function          (on)
import           Data.List              (groupBy, sortBy)

type CommandName = String
type Description = D.Doc
data CommandSpec a
  = NoArgCommand  !CommandName  !a                     !Description
  | StringCommand !CommandName  !(String -> a) !String !Description

data CommandTrie a
  = Exec   !String !(String -> a)
  | Choice !(M.Map Char (CommandTrie a))

commandUsage :: [CommandSpec a] -> Doc
commandUsage spec = D.align $ D.vsep $ map pprCommand spec
  where
    pprCommand (NoArgCommand c _ d) =
      D.nest 4 (D.text c D.<$> d)
    pprCommand (StringCommand c _ a d) =
      D.nest 4 (D.text c D.<+> D.text a D.<$> d)

parseCommand :: [CommandSpec a] -> (String -> a) -> String -> a
parseCommand spec cont initStr = go initTrie initStr
  where
    initTrie = makeTrie spec

    go (Exec [] f)  str = f $ dropWhile isSpace str
    go (Exec _ f) []  = f []
    go (Exec (r:residual) f) (c:cs) | r == c = go (Exec residual f) cs
    go (Exec _ f) (c:cs) | isSpace c = f $ dropWhile isSpace cs
    go (Exec _ _) _ = cont initStr
    go (Choice mp) (c:cs) = case M.lookup c mp of
      Just tr -> go tr cs
      Nothing -> cont initStr
    go _ _ = cont initStr

makeTrie :: [CommandSpec a] -> CommandTrie a
makeTrie spec = h (groupByFirstChar $ sortBy (compare `on` fst) $ map normalize spec)
  where
    groupByFirstChar = groupBy ((==) `on` head' . fst)
      where
        head' []    = Nothing
        head' (x:_) = Just x

    normalize (NoArgCommand s f _)    = (s, const f)
    normalize (StringCommand s f _ _) = (s, f)

    h [[(s,f)]] = Exec s f -- there is only one choice for the first letter.
    h xss = Choice $ M.fromList $
            map (\xs@((a:_,_):_) -> (a, h (groupByFirstChar $ map (first tail) xs))) xss
