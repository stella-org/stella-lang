-- | Why the JavaScript backend refuses a module.
module Stella.Backend.JavaScript.Error
  ( JsError(..)
  ) where

import Prelude

import Prim as P

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Bytecode.Bytes (EncodeError)
import Stella.Compiler.TypedCore.Name (EffName, Ident, ModuleName, Qualified)

data JsError
  -- | A construct this backend does not generate, named by what it is.
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
  -- | A foreign whose name the ABI fixes as an entry the runtime carries out — an
  -- | operation, or `Base.IO.pure` or `Base.IO.bind` — declared at another arity, as
  -- | the ABI's and the declaration's. The name selects the entry, so the
  -- | declaration is not a declaration of it.
  | EntryDeclaredAtWrongArity (Qualified Ident) P.Int P.Int
  -- | A foreign a host must implement, declared by a module given no manifest entry.
  | ForeignWithoutImplementation (Qualified Ident)
  -- | A foreign the module's manifest entry gives no signature, which its values
  -- | would cross by.
  | NoSignature (Qualified Ident)
  -- | A foreign whose signature has `params` of another length than the arity
  -- | declared, as the declared arity and the length. The two came from the same
  -- | compiler, or a manifest and a module that do not belong together.
  | SignatureDisagrees (Qualified Ident) P.Int P.Int
  -- | An entry point naming no global of the module.
  | NoEntryGlobal (Qualified Ident)
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
  -- | A region declaring one cell twice, as the key's canonical string, or a
  -- | handler holding two clauses for one operation, as its name. Two indices may
  -- | hold one key or one name, so what is compared is what they hold.
  | CellKeyTwice P.String
  | ClauseTwice P.String
  -- | A `HNDL` or `TAILHNDL` supplying another count of clauses than its handler
  -- | entry holds: the canonical string of the handler's key, the entry's count,
  -- | and the instruction's.
  | HandlerClausesDisagree P.String P.Int P.Int
  -- | A `RGN` or `TAILRGN` supplying another count of initial values than its
  -- | region entry has cells: the canonical strings of the cells' keys, and the
  -- | instruction's count.
  | RegionCellsDisagree (P.Array P.String) P.Int

derive instance Eq JsError
derive instance Generic JsError _

instance Show JsError where
  show = genericShow
