module AbsPawel where

import Data.Map (Map, empty)
import qualified Text.PrettyPrint as PP

data Program = Prog [Decl]
    deriving (Eq, Ord, Show, Read)

data Decl
    = DExp Idt [TypeDecl] Exp
    | DLOp Integer Idt Idt
    | DROp Integer Idt Idt
    | DType Idt [Idt] [Variant]
    deriving (Eq, Ord, Show, Read)

data Variant = VarType Idt [Type]
    deriving (Eq, Ord, Show, Read)

data Type = TInt | TVar Idt | TFunc Type Type | TVariant Idt [Type] | TOverload [Type]
    deriving (Eq, Ord, Read)

data Scheme = Scheme [Idt] Type deriving (Eq)
newtype TypeEnv = TypeEnv (Map Idt Scheme) deriving (Eq, Show)

data Exp
    = EUnparsed [Exp]
    | EVar Idt
    | EInt Integer
    | ELet Idt [TypeDecl] Exp Exp
    | EIf Exp Exp Exp
    | ELam [Idt] Exp
    | EMatch Idt [MatchCase]
    | EApp Exp Exp
    deriving (Eq, Ord, Show, Read)

data MatchCase = Case Match Exp
    deriving (Eq, Ord, Show, Read)

data Match = MVar Idt | MList [Match] | MCons Idt [Match]
    deriving (Eq, Ord, Show, Read)

data TypeDecl = TDVar Idt | TDType Idt Type
    deriving (Eq, Ord, Show, Read)

newtype Idt = Idt String
    deriving (Eq, Ord, Read)
instance Show Idt where
    show (Idt x) = x

untype :: TypeDecl -> Idt
untype (TDVar x) = x
untype (TDType x _) = x

data ExpBound
    = EBVar Idt
    | EOVar Int Idt
    | EBInt Integer
    | EBVariant Idt [ExpBound]
    | EBIf ExpBound ExpBound ExpBound
    | EBLet Idt [TypeDecl] ExpBound ExpBound
    | EBLam BEnv [Idt] ExpBound
    | EBMatch Idt [MatchCaseBound]
    | EOMatch Int Idt [MatchCaseBound]
    | EBApp ExpBound ExpBound
    | EBOverload [ExpBound]
    | EBArith ExpBound ExpBound AriOp
    deriving (Eq, Ord, Read)

type BEnv = Map Idt ExpBound

newtype AriOp = AriOp (Integer -> Integer -> Maybe Integer)
instance Show AriOp where
    show (AriOp f) = case f 15 4 of
        Just 19 -> "+"
        Just 11 -> "-"
        Just 60 -> "*"
        Just 3 -> "/"
        Just 1 -> case f 15 15 of
            Just 1 -> ">="
            Just 0 -> ">"
        Just 0 -> case f 15 15 of
            Just 1 -> case f 15 16 of
                Just 1 -> "<="
                Just 0 -> "=="
            Just 0 -> "<"
instance Eq AriOp where
    a == b = show a == show b
instance Ord AriOp where
    compare a b = compare (show a) (show b)
instance Read AriOp where
    readsPrec a b = case b of
        "+" -> [(ariOp (+), "")]
        "-" -> [(ariOp (-), "")]
        "*" -> [(ariOp (*), "")]
        "/" -> [(ariOp div, "")]
        ">=" -> [(ariOp (\x y -> if x >= y then 1 else 0), "")]
        ">" -> [(ariOp (\x y -> if x > y then 1 else 0), "")]
        "<=" -> [(ariOp (\x y -> if x <= y then 1 else 0), "")]
        "<" -> [(ariOp (\x y -> if x < y then 1 else 0), "")]
        "==" -> [(ariOp (\x y -> if x == y then 1 else 0), "")]
        _ -> []
ariOp f = AriOp (\x y -> Just $ f x y)
ari f = EBLam empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") f

data MatchCaseBound = CaseBound Match ExpBound | CaseBoundOverload [MatchCaseBound]
    deriving (Eq, Ord, Show, Read)

instance Show ExpBound where
    showsPrec _ x = shows (prExp x)

prExp :: ExpBound -> PP.Doc
prExp (EBVar x) = PP.text (show x)
prExp (EOVar n x) = PP.text (show x)
prExp (EBInt x) = PP.text (show x)
prExp (EBVariant x []) = PP.text (show x)
prExp (EBVariant x xs) = 
    PP.text (show x) 
    PP.<> PP.parens (PP.hcat (PP.punctuate PP.comma (map prExp xs)))
prExp (EBIf e1 e2 e3) =
    PP.text "if"
    PP.<+> prExp e1
    PP.<+> PP.text "then"
    PP.$$ PP.nest 2 (prExp e2)
    PP.$$ PP.text "else"
    PP.$$ PP.nest 2 (prExp e3)
prExp (EBLet x tds e1 e2) =
    PP.text "let" 
    PP.<+> PP.text (show x) 
    PP.<+> PP.text "=" 
    PP.<+> prExp e1 
    PP.<+> PP.text "in" 
    PP.$$ PP.nest 2 (prExp e2)
prExp (EBLam env [] e) = PP.text "\955_." PP.<+> prExp e
prExp (EBLam env xs e) = 
    PP.text "\955" 
    PP.<+> PP.hcat (PP.punctuate (PP.text " ") (map PP.text (map show xs))) 
    PP.<+> PP.text "." 
    PP.<+> prExp e
prExp (EOMatch n x cs) = prExp (EBMatch x cs)
prExp (EBMatch x cs) = 
    PP.text "match"
    PP.<+> PP.text (show x)
    PP.<+> PP.text "with"
    PP.$$ PP.nest 2 (PP.vcat (map prMatchCase cs))
prExp (EBApp e1 e2) = prParenExpL e1 PP.<+> prParenExpR e2
prExp (EBOverload xs) = 
    PP.text "overload" 
    PP.<+> PP.parens (PP.cat (PP.punctuate PP.comma (map prExp xs)))
prExp (EBArith e1 e2 op) = 
    prParenExpL e1 
    PP.<+> PP.text (show op) 
    PP.<+> prParenExpL e2

prMatchCase :: MatchCaseBound -> PP.Doc
prMatchCase (CaseBound m e) = 
    prMatch m 
    PP.<+> PP.text "->" 
    PP.<+> prExp e

prMatch :: Match -> PP.Doc
prMatch (MCons x xs) = 
    PP.text (show x) 
    PP.<+> PP.hcat (PP.punctuate (PP.text " ") (map prParenMatch xs))
prMatch (MVar x) = PP.text (show x)

prParenMatch :: Match -> PP.Doc
prParenMatch t = case t of
    MCons _ (_ : _) -> PP.parens (prMatch t)
    _ -> prMatch t

prParenExpL :: ExpBound -> PP.Doc
prParenExpL t = case t of
    EBVariant _ _ -> PP.parens (prExp t)
    EBIf _ _ _ -> PP.parens (prExp t)
    EBLet _ _ _ _ -> PP.parens (prExp t)
    EBLam _ _ _ -> PP.parens (prExp t)
    EBMatch _ _ -> PP.parens (prExp t)
    EBOverload _ -> PP.parens (prExp t)
    EBArith _ _ _ -> PP.parens (prExp t)
    _ -> prExp t

prParenExpR :: ExpBound -> PP.Doc
prParenExpR t = case t of
    EBApp _ _ -> PP.parens (prExp t)
    _ -> prParenExpL t

instance Show Type where
    showsPrec _ x = shows (prType x)

prType :: Type -> PP.Doc
prType (TVar n) = PP.text (show n)
prType TInt = PP.text "Int"
prType (TFunc t s) = 
    prParenType t 
    PP.<+> PP.text "->" 
    PP.<+> prType s
prType (TVariant n ts) = 
    PP.text (show n) 
    PP.<> PP.parens (PP.hcat (PP.punctuate PP.comma (map prType ts)))
prType (TOverload ts) = 
    PP.text "overload" 
    PP.<> PP.parens (PP.cat (PP.punctuate PP.comma (map prType ts)))

prParenType :: Type -> PP.Doc
prParenType t = case t of
    TFunc _ _ -> PP.parens (prType t)
    _ -> prType t

instance Show Scheme where
    showsPrec _ (Scheme [] t) = shows t
    showsPrec _ x = shows (prScheme x)

prScheme :: Scheme -> PP.Doc
prScheme (Scheme vars t) =
    PP.text "Forall"
    PP.<+> PP.hcat (PP.punctuate PP.comma (map PP.text $ map show vars))
    PP.<> PP.text "."
    PP.<+> prType t

