-- File generated by the BNF Converter (bnfc 2.9.4.1).

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The abstract syntax of language Pawel.

module AbsPawel where

import Prelude (Integer, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

data Program = Prog [Decl]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Decl
    = DExp Idt [TypeDecl] Exp
    | DLOp Integer Idt Idt
    | DROp Integer Idt Idt
    | DType Idt [Idt] [Variant]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Variant = VarType Idt [Type]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Type = TInt | TVar Idt | TFunc Type Type | TVariant Idt [Type]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Exp
    = EUnparsed [Exp]
    | EVar Idt
    | EInt Integer
    | ELet Idt [TypeDecl] Exp Exp
    | EIf Exp Exp Exp
    | ELam [Idt] Exp
    | EMatch Idt [MatchCase]
    | EApp Exp Exp
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data MatchCase = Case Match Exp
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Match = MVar Idt | MList [Match] | MCons Idt [Match]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TypeDecl = TDVar Idt | TDType Idt Type
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype Idt = Idt String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

