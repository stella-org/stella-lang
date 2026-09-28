-- | Why the JavaScript backend refuses a module.
module Stella.Compiler.JavaScript.Error
  ( JsError(..)
  ) where

import Prelude

import Prim as P

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Bytecode.Bytes (EncodeError)
import Stella.Compiler.TypedCore.Name (EffName, Ident, ModuleName, Qualified)

data JsError
  -- | A construct this backend does not generate code for yet, named by what it
  -- | is.
  = Unsupported P.String
  -- | A module an encoder refuses to write, for the reason it gives. A module
  -- | handed across without its bytes is accepted exactly where its bytes would
  -- | have been written and read back.
  | NotEncodable EncodeError
  -- | A module under a name the implicit environment holds. `Prim` is Core's own
  -- | vocabulary and no file declares it.
  | ReservedModuleName ModuleName
  -- | A declaration whose qualified name belongs to another module, or a
  -- | constructor whose owner type does.
  | NotThisModule (Qualified Ident)
  | OwnerNotThisModule (Qualified Ident)
  | EffectNotThisModule (Qualified EffName)
  -- | Two declarations of one name in one namespace. The values of a module are
  -- | one namespace, so a global and a foreign of one name collide.
  | DeclaredTwice (Qualified Ident)
  | EffectDeclaredTwice (Qualified EffName)
  -- | An exported name that is not a value this module declares.
  | ExportNotDeclared (Qualified Ident)
  -- | A global installed as a function of no parameters: a definitional arity
  -- | counts leading lambdas and is at least one.
  | FunctionGlobalWithoutParameters (Qualified Ident)
  -- | A global evaluated at initialization whose function takes parameters. It is
  -- | entered with none.
  | RunGlobalWithParameters (Qualified Ident) P.Int
  -- | A global whose function expects captures. A global is installed over an
  -- | empty capture list.
  | GlobalExpectsCaptures (Qualified Ident) P.Int
  -- | A foreign whose name the ABI fixes as an operation, declared at another
  -- | arity, as the ABI's and the declaration's.
  | OperationDeclaredAtWrongArity (Qualified Ident) P.Int P.Int
  -- | A reference to a module the module does not import. A header says which
  -- | modules a term may name.
  | NotImported (Qualified Ident)
  -- | A reference into this module that names no declaration of the kind the
  -- | table it stands in calls for.
  | NoSuchDeclaration (Qualified Ident)
  -- | An index no table of the module holds.
  | NoSuchIndex P.String P.Int
  -- | A call or a partial application whose count its callee does not admit: a
  -- | known call supplies the definitional arity, a saturated constructor its
  -- | arity, and a partial application fewer.
  | ArityMismatch P.String P.Int P.Int
  -- | A join point a transfer names and the function does not declare, or
  -- | declares twice.
  | NoSuchJoin P.Int P.Int
  | JoinTwice P.Int P.Int

derive instance Eq JsError
derive instance Generic JsError _

instance Show JsError where
  show = genericShow
