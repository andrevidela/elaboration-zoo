module Main

import Data.Maybe
import Data.List

import Text.Lex
import Text.Parse
import Text.PrettyPrint.Prettyprinter.Doc

import Derive.Prelude


%hide TT.Name
%language ElabReflection

-- syntax
--------------------------------------------------------------------------------

Name : Type
Name = String

data Tm
  = Var Name           -- x
  | Lam Name Tm        -- \x. t
  | App Tm Tm          -- t u
  | Let Name Tm Tm     -- let x = t; u

-- evaluation
--------------------------------------------------------------------------------

data Val
  = VVar Name
  | VApp Val (Lazy Val)
  | VLam Name (Val -> Val)

Env : Type
Env = List (Name, Val)

fresh : List Name -> Name -> Name
fresh ns "_" = "_"
fresh ns x   = case elem x ns of
  True  => fresh ns (x ++ "'")
  False => x

private infixl 2 $$

($$) : Val -> Val -> Val
($$) (VLam _ t) u = t u
($$) t          u = VApp t u

partial
eval : Env -> Tm -> Val
eval env =
  \case
    (Var x)     => let (Just v) = lookup x env in v
    (App t u)   => eval env t $$ eval env u
    (Lam x t)   => VLam x (\u => eval ((x, u)::env) t)
    (Let x t u) => eval ((x, eval env t)::env) u

quote : List Name -> Val -> Tm
quote ns =
  \case
  (VVar x)   => Var x
  (VApp t u) => App (quote ns t) (quote ns u)
  (VLam y t) => let x = fresh ns y in Lam x (quote (x::ns) (t (VVar x)))

partial
nf : Env -> Tm -> Tm
nf env = quote (map fst env) . eval env

-- parsing
--------------------------------------------------------------------------------

data LambdaToken
  = LamTok | In | LetTok | EqTok | Dot | Ident String | LParen | RParen

%runElab derive "LambdaToken" [Eq]

Interpolation LambdaToken where
  interpolate LamTok = "λ"
  interpolate In = "in"
  interpolate LetTok = "let"
  interpolate EqTok = "="
  interpolate Dot = "."
  interpolate (Ident str) = str
  interpolate LParen = "("
  interpolate RParen = ")"

idLexer : Lexer
idLexer = pred isAlpha <++> preds isAlphaNum

lambdaTokenMap : TokenMap LambdaToken
lambdaTokenMap =
  [ (is 'λ' , const LamTok)
  , (is '.' , const Dot)
  , (is '=' , const EqTok)
  , (is '(' , const RParen)
  , (is ')' , const LParen)
  , (exact "in" , const In)
  , (idLexer , Ident . cast)
  ]

0 Rule : Bool -> Type -> Type
Rule b t = Grammar b () LambdaToken String t

term : Rule True Tm

identifier : Rule True String
identifier = terminal (\case (Ident str) => Just str ; _ => Nothing)

variable : Rule True Tm
variable = Var <$> identifier

atom : Rule True Tm
atom = variable <|> is LParen *> term <* is RParen

app : Rule True Tm
app = foldl1 App <$> some atom

lambda : Rule True Tm
lambda = do
  is LamTok
  name <- identifier
  is Dot
  tm <- term
  pure $ Lam name tm

letTerm : Rule True Tm
letTerm = do
  is LetTok
  name <- identifier
  is EqTok
  expr <- term
  is In
  body <- term
  pure $ Let name expr body

term = lambda <|> letTerm <|> app

prettyTerm : Bool -> Tm -> Doc ann
prettyTerm k (Var s) = pretty s
prettyTerm k (Lam str x) = "λ" <++> pretty str <++> softline <+> "." <++> prettyTerm False x
prettyTerm k (App x y) =
  let app : Doc ann = prettyTerm False x <++> prettyTerm True y
  in if k then Doc.surround {ann} "(" ")" app else app
prettyTerm k (Let str expr body) =
  "let" <++> pretty str <++> "=" <++> prettyTerm False expr <++>
  softline <+> "in" <++> prettyTerm False body

Pretty Tm where
  pretty = prettyTerm False

