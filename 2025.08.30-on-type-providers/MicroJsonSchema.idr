module MicroJsonSchema

-- public expors here as a workaround for elab scripts
import public Data.List
import public Data.SnocList

import public JSON.Parser
import public JSON.Simple.Derive

----------------------------------
--- Reexports for derived code ---
----------------------------------
import public Data.List.Quantifiers
import public Data.Nat
import public Data.So
import public Text.Regex
----------------------------------

%default total
%language ElabReflection

record KVList k v where
  constructor MkKVList
  unKVList : List (k, v)

FromJSONKey k => FromJSON v => FromJSON (KVList k v) where
  fromJSON = withObject "KVList" $ map (MkKVList . cast) . go empty where
    go : SnocList (k, v) -> Parser (List (String,JSON)) (SnocList (k, v))
    go acc []            = pure acc
    go acc ((k, v)::kvs) = go (acc :< (!(fromKey k), !(fromJSON v))) kvs

||| Describes a tiny strictly typed subset of JsonSchema 2020-12
data JsonSchema : Type where
  SObject : (properties : KVList String JsonSchema) -> JsonSchema
  SArray : (items : JsonSchema) ->
           (minItems, maxItems : Maybe Integer) ->
           JsonSchema
  SString : (pattern : String) -> JsonSchema
  SInteger : (minimum, maximum : Maybe Integer) -> JsonSchema

jsonSchemaDerivationOpts = MkOptions
  { sum = UntaggedValue -- TaggedObject "type" "c" -- doesn't work as should
  , replaceMissingKeysWithNull = True
  , unwrapRecords = True
  , unwrapUnary = False
  , constructorTagModifier = pack . drop 1 . map toLower . unpack
  , fieldNameModifier = id
  }

%runElab derive `{JsonSchema} [ customFromJSON Private jsonSchemaDerivationOpts ]

public export
data SchemaSource = File String | Str String

loadJsonSchema : SchemaSource -> Elab JsonSchema
loadJsonSchema shs = do
  s <- case shs of
         Str s => pure s
         File path => maybe (fail "can't read file \{path} in the project dir") pure =<< readFile ProjectDir path
  let Right json = parseJSON Virtual s
    | Left err => fail "can't parse: \{show err}"
  let Right sch = fromJSON json
    | Left err => fail "bad schema: \{show err}"
  pure sch

record DerivationResult where
  constructor DR
  declarations : List Decl
  constraints  : List $ Name -> TTImp
  type         : TTImp

prepareFieldName : (jsonName : String) -> Name
prepareFieldName jsonName = do
  let jsonName = unpack jsonName <&> \c => if isAlphaNum c || c == '_' then c else '_'
  fromString $ case jsonName of
    []          => "x"
    xs@('_'::_) => pack $ 'a'::xs
    x::xs       => pack $ toLower x :: xs

autoFieldsToSig : Name -> List (Name -> TTImp) -> (resultTy : TTImp) -> TTImp
autoFieldsToSig _ []      = id
autoFieldsToSig n (c::cs) = IPi EmptyFC M0 AutoImplicit Nothing (c n) . autoFieldsToSig n cs

fieldsToSig : List (Name, DerivationResult) -> (resultTy : TTImp) -> TTImp
fieldsToSig []                      = id
fieldsToSig ((n, DR _ cs ty) :: xs) = IPi EmptyFC MW ExplicitArg (Just n) ty . autoFieldsToSig n cs . fieldsToSig xs

mapFirstChar : (Char -> Char) -> String -> String
mapFirstChar f str = case unpack str of
  x::xs => pack $ f x :: xs
  []    => "Unknown"

%inline
up : String -> String
up = mapFirstChar toUpper

-- Makes namespace except the last element and returns the its last element separately
mkNS : Name -> (String, Namespace)
mkNS (NS (MkNS ns) nm) = let (last, MkNS subns) = mkNS nm in (last, MkNS $ subns ++ ns)
mkNS (UN (Basic str))  = let n = up str in (n, MkNS $ pure n)
mkNS (UN (Field str))  = let n = up str in (n, MkNS $ pure n)
mkNS (UN Underscore)   = let n = "Underscore" in (n, MkNS $ pure n)
mkNS (MN str i)        = let n = up str in (n, MkNS $ pure n)
mkNS (DN str nm)       = mkNS nm
mkNS (Nested x nm)     = mkNS nm
mkNS (CaseBlock str i) = let n = up str in (n, MkNS $ pure n)
mkNS (WithBlock str i) = let n = up str in (n, MkNS $ pure n)

andThen : Namespace -> Namespace -> Namespace
andThen (MkNS ls) (MkNS rs) = MkNS $ rs ++ ls -- namespaces are unfortunately stored in reverse order

-- Return derived type expression and a list of appropriate declarations
deriveJsonType : (outerNS : Namespace) -> Name -> JsonSchema -> DerivationResult
deriveJsonType oNS nsN $ SObject properties = do
  let (tySuff, ns) = mkNS nsN
  let oiNS = oNS `andThen` ns
  let fields = unKVList properties <&> \(n, js) => let n = prepareFieldName n in (n, assert_total deriveJsonType oiNS n js)
  let subds = fields >>= declarations . snd
  let tyN = UN $ Basic $ tySuff ++ "Ty"
  let newD = INamespace EmptyFC ns $ subds ++ do
               let newC = UN $ Basic $ "Mk" ++ tySuff
               let dat = IData EmptyFC (SpecifiedValue Public) (Just Total) $
                           MkData EmptyFC tyN (Just $ IType EmptyFC) [] $ pure $
                             MkTy EmptyFC (NoFC newC) $
                               fieldsToSig fields $ IVar EmptyFC tyN
               let accessorLHSArgs = foldl (\l, (n, _) => INamedApp EmptyFC l n (IVar EmptyFC n)) (IVar EmptyFC newC) fields
               let fieldAccessors = fields >>= \(n, DR _ _ ty) => let accN = UN $ Field $ show n in
                                      [ IClaim $ NoFC $ MkIClaimData MW Public [] $ MkTy EmptyFC (NoFC accN) $
                                          IPi EmptyFC MW ExplicitArg Nothing (IVar EmptyFC tyN) ty
                                      , IDef EmptyFC accN $ singleton $
                                          PatClause EmptyFC (IApp EmptyFC (IVar EmptyFC accN) accessorLHSArgs) (IVar EmptyFC n)
                                      ]
               dat :: fieldAccessors
  DR [newD] empty $ IVar EmptyFC $ NS oiNS tyN
deriveJsonType oNS nsN $ SArray items minItems maxItems = do
  let DR subds subcs subty = deriveJsonType oNS nsN items
  let m = UN $ Basic "^x^" -- internal lambda's name
  let subcs = subcs <&> \c, n => `(Data.List.Quantifiers.All.All ~(ILam EmptyFC MW ExplicitArg (Just m) subty $ c m) ~(IVar EmptyFC n))
  let lLen = minItems <&> \mi, n => `(fromInteger ~(IPrimVal EmptyFC $ BI mi) `Data.Nat.LTE` length ~(IVar EmptyFC n))
  let rLen = maxItems <&> \ma, n => `(length ~(IVar EmptyFC n) `Data.Nat.LTE` fromInteger ~(IPrimVal EmptyFC $ BI ma))
  DR subds (subcs ++ mapMaybe id [lLen, rLen]) `(Prelude.List ~subty)
deriveJsonType oNS nsN $ SString pat = do
  let (rxN, ns) = mkNS nsN
  let rxN = UN $ Basic $ mapFirstChar toLower rxN ++ "Regex"
  let patDs = [ IClaim $ NoFC $ MkIClaimData MW Public [] $ MkTy EmptyFC (NoFC rxN) `(Text.Regex.Naive.RegExp ?)
              , IDef EmptyFC rxN $ singleton $ PatClause EmptyFC (IVar EmptyFC rxN) `(~(IPrimVal EmptyFC $ Str pat).erx)
              ]
  let patConstraint = \n => `(Text.Matcher.MatchesWhole ~(IVar EmptyFC $ NS oNS rxN) ~(IVar EmptyFC n))
  DR patDs [patConstraint] $ IPrimVal EmptyFC $ PrT StringType
deriveJsonType _ _ $ SInteger mi ma = if mi >= Just 0 -- we use fact that `Nothing` < `Just _`
  then do
    let lConstraint = mi >>= \mi => whenT (mi > 0) $ \n => `(fromInteger ~(IPrimVal EmptyFC $ BI mi) `Data.Nat.LTE` ~(IVar EmptyFC n))
    let rConstraint = ma <&> \ma, n => `(~(IVar EmptyFC n) `Data.Nat.LTE` fromInteger ~(IPrimVal EmptyFC $ BI ma))
    DR empty (mapMaybe id [lConstraint, rConstraint]) `(Prelude.Nat)
  else do
    let lConstraint = mi <&> \mi, n => `(So $ ~(IPrimVal EmptyFC $ BI mi) <= ~(IVar EmptyFC n))
    let rConstraint = ma <&> \ma, n => `(So $ ~(IVar EmptyFC n) <= ~(IPrimVal EmptyFC $ BI ma))
    DR empty (mapMaybe id [lConstraint, rConstraint]) $ IPrimVal EmptyFC $ PrT $ IntegerType

deriveToplevelJsonType : Name -> JsonSchema -> Elab (List Decl, TTImp)
deriveToplevelJsonType n js = do
  let DR decls [] ty = case deriveJsonType (MkNS []) n js of
                         dr@(DR _ [] _) => dr
                         _ => deriveJsonType (MkNS []) n $ SObject $ MkKVList $ pure ("value", js)
    | _ => fail "can't derive a type without additional constraints"
  pure (decls, ty)

prepareTyName : SnocList Name -> Name
prepareTyName = UN . Basic . joinBy "_" . map (show . dropNS) . toList

export
deriveJsonSchema : SchemaSource -> Elab Type
deriveJsonSchema shs = do
  n <- prepareTyName <$> getCurrentFn
  (decls, ty) <- deriveToplevelJsonType n =<< loadJsonSchema shs
  declare decls
  check ty
