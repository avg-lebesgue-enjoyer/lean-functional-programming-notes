/- @file Notes/Chapter6/Sec6Complete.lean
 - @src https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad/complete.html
 -/
namespace ν

/- SECTION: `Functor` -/
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    map ∘ (Function.const _)

#print Function.const

/- SECTION: `Applicative` -/

class Pure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α

class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β

class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

class Applicative (f : Type u → Type v)
  extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f
  where
    map      := fun x y => Seq.seq (pure x) fun _ => y
    seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
    seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b



/- SECTION: `Monad` -/

class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()

end ν



/- EXERCISES: Show that `[Applicative m] → Applicative.map m = Functor.map m` -/

class SeqPure.{u, v} (T : Type u → Type v) : Type (max u v + 1) where
  toSeq  : Seq T
  toPure : Pure T
instance [SeqPure T] : Seq T  := SeqPure.toSeq
instance [SeqPure T] : Pure T := SeqPure.toPure

def SeqPure.map.{u, v} {T : Type u → Type v} [Seq T] [Pure T]
  : {α β : Type u} → (f : α → β) → T α → T β
  := fun f ta =>
    pure f <*> ta

-- Look, the ones burnt into Lean's `LawfulApplicative` already have an axiom that just says `(pure · <*> ·) = (· <$> ·)` in there,
--  so I wasn't gonna cheat and use that...
-- So, I stole the Haskell laws instead.
class LawfulSeqPure.{u, v} (T : Type u → Type v) [Seq T] [Pure T] : Prop where
  identity : ∀ {α : Type u} (ta : T α),
    pure id <*> ta = ta
  homomorphism : ∀ {α β : Type u} (f : α → β) (a : α),
    pure f <*> pure a = pure (f a)   (f := T)
  interchange : ∀ {α β : Type u} (tf : T (α → β)) (a : α),
    tf <*> pure a = pure (· a) <*> tf
  composition : ∀ {α β γ : Type u} (tg : T (β → γ)) (tf : T (α → β)) (ta : T α),
    pure (· ∘ ·) <*> tg <*> tf <*> ta = tg <*> (tf <*> ta)

theorem SeqPure.id_map.{u, v} (T : Type u → Type v) [SeqPure T] [law : LawfulSeqPure T]
  : ∀ {α : Type u} (ta : T α),
    SeqPure.map id ta = ta
  := by
    unfold map
    exact law.identity

theorem SeqPure.comp_map.{u, v} (T : Type u → Type v) [SeqPure T] [law : LawfulSeqPure T]
  : ∀ {α β γ : Type u} (f : α → β) (g : β → γ) (ta : T α),
    SeqPure.map (g ∘ f) ta = SeqPure.map g (SeqPure.map f ta)
  := by
    intro α β γ f g ta
    unfold map
    rw  [←law.composition
        , law.homomorphism
        , law.homomorphism]

instance instFunctorOfSeqPure.{u, v}
  {T : Type u → Type v} [SeqPure T]
  : Functor T
  where
    map := SeqPure.map

instance instLawfulFunctorOfLawfulSeqPure.{u, v}
  {T : Type u → Type v} [SeqPure T] [LawfulSeqPure T]
  : LawfulFunctor T
  where
    map_const := rfl
    id_map := @SeqPure.id_map T inferInstance inferInstance
    comp_map := @SeqPure.comp_map T inferInstance inferInstance
-- Verification successful



/- EXERCISES: Show that a `LawfulMonad` yields a `LawfulApplicative` -/

class BindPure.{u, v} (T : Type u → Type v) : Type (max u v + 1) where
  toBind : Bind T
  toPure : Pure T
instance [BindPure T] : Bind T := BindPure.toBind
instance [BindPure T] : Pure T := BindPure.toPure

#check Seq.seq
-- Seq.seq.{u, v} {f : Type u → Type v} [self : Seq f]
--  {α β : Type u} : f (α → β) → (Unit → f α) → f β


def BindPure.map.{u, v} {T : Type u → Type v} [Bind T] [Pure T]
  : {α β : Type u} → (f : α → β) → T α → T β
  := fun f Ta =>
    Ta >>= (pure ∘ f)

def BindPure.seq.{u, v} {T : Type u → Type v} [Bind T] [Pure T]
  : {α β : Type u} → (Tf : T (α → β)) → (Unit → T α) → T β
  := fun Tf lTa =>
    Tf >>= fun f =>
      BindPure.map f (lTa ())

class LawfulBindPure.{u, v} (T : Type u → Type v) [BindPure T] : Prop where
  leftIdentity {α β : Type u} : ∀ (a : α) (f : α → T β),
    pure a >>= f  =  f a
  rightIdentity {α : Type u} : ∀ (Ta : T α),
    Ta >>= pure  =  Ta
  assoc {α β γ : Type u} : ∀ (Ta : T α) (f : α → T β) (g : β → T γ),
    Ta >>= f >>= g  =  Ta >>= (f · >>= g)

instance instFunctorOfBindPure.{u, v}
  {T : Type u → Type v} [BindPure T]
  : Functor T
  where
    map := BindPure.map

instance instApplicativeOfBindPure.{u, v}
  {T : Type u → Type v} [BindPure T]
  : Applicative T
  where
    pure := BindPure.toPure.pure
    seq  := BindPure.seq

theorem BindPure.id_map.{u, v}
  {T : Type u → Type v} [BindPure T] [law : LawfulBindPure T]
  : ∀ {α : Type u} (Ta : T α), id <$> Ta = Ta
  := by
    intro α Ta
    show BindPure.map id Ta = Ta
    unfold BindPure.map
    show Ta >>= (pure ∘ id)  =  Ta
    have : pure ∘ id = pure (f := T) (α := α) := by
      apply funext ; intro a
      rw [ Function.comp_apply
          ,id_def]
    rw [this]
    show Ta >>= pure  =  Ta
    apply law.rightIdentity
  -- [done.]

theorem BindPure.comp_map.{u, v}
  {T : Type u → Type v} [BindPure T] [law : LawfulBindPure T]
  : ∀ {α β γ : Type u} (f : α → β) (g : β → γ) (Ta : T α),
    (g ∘ f) <$> Ta  =  g <$> f <$> Ta
  := by
    intro α β γ f g Ta
    show BindPure.map (g ∘ f) Ta = BindPure.map g (BindPure.map f Ta)
    unfold BindPure.map
    rw [law.assoc]
    show Ta >>= pure ∘ g ∘ f
          = Ta >>= ((pure ∘ f) · >>= pure ∘ g)
    have : ((pure ∘ f) · >>= pure ∘ g)
            = (pure (f := T)) ∘ g ∘ f
        := by
          apply funext ; intro a
          rw  [ Function.comp_apply
              , law.leftIdentity
              , Function.comp_apply
              , Function.comp_apply
              , Function.comp_apply]
    rw [this]
  -- [done.]

instance instLawfulFunctorOfLawfulBindPure.{u, v}
  {T : Type u → Type v} [BindPure T] [LawfulBindPure T]
  : LawfulFunctor T
  where
    map_const := rfl
    id_map := @BindPure.id_map T inferInstance inferInstance
    comp_map := @BindPure.comp_map T inferInstance inferInstance
  -- [done.]

theorem BindPure.map_pure.{u, v}
  {T : Type u → Type v} [BindPure T] [law : LawfulBindPure T]
  : ∀ {α β : Type u} (f : α → β) (a : α),
    f <$> pure a = (pure (f := T)) (f a)
  := by
    intro α β f a
    show BindPure.map f (pure a) = pure (f a)
    unfold map
    show pure a >>= pure ∘ f = pure (f a)
    rw  [ law.leftIdentity
        , Function.comp_apply]
    -- [done.]

theorem BindPure.seqLeft_eq.{u, v}
  {T : Type u → Type v} [BindPure T] [LawfulBindPure T]
  : ∀ {α β : Type u} (Ta : T α) (Tb : T β),
    Ta <* Tb = Function.const β <$> Ta <*> Tb
  := by
    intros
    unfold SeqLeft.seqLeft Applicative.toSeqLeft
    rfl
    -- [done.]

theorem BindPure.seqRight_eq.{u, v}
  {T : Type u → Type v} [BindPure T] [LawfulBindPure T]
  : ∀ {α β : Type u} (Ta : T α) (Tb : T β),
    Ta *> Tb = Function.const α id <$> Ta <*> Tb
  := by
    intros
    unfold SeqRight.seqRight Applicative.toSeqRight
    rfl
    -- [done.]

theorem fun_apply.{u, v}
  {α : Type u} {β : Type v}
  (g : α → β)
  (a : α)
  : (g ·) a = g a
  := rfl

theorem comp_fun.{u, v, w}
  {α : Type u} {β : Type v} {γ : Type w}
  (g : β → γ) (f : α → β)
  : g ∘ (fun x => f x) = fun x => g (f x)
  := rfl

theorem BindPure.pure_seq.{u, v}
  {T : Type u → Type v} [BindPure T] [law : LawfulBindPure T]
  : ∀ {α β : Type u} (f : α → β) (Ta : T α),
    pure f <*> Ta = f <$> Ta
  := by
    intro α β f Ta
    show BindPure.seq (pure f) (fun () => Ta)
          = BindPure.map f Ta
    unfold BindPure.seq
    rw  [ fun_apply (fun x => Ta) ()
        , law.leftIdentity]
    -- [done.]

theorem BindPure.seq_pure.{u, v}
  {T : Type u → Type v} [BindPure T] [law : LawfulBindPure T]
  : ∀ {α β : Type u} (Tf : T (α → β)) (a : α),
    Tf <*> pure a = (· a) <$> Tf
  := by
    intro α β Tf a
    show BindPure.seq Tf (fun () => pure a)
          = BindPure.map (· a) Tf
    unfold BindPure.seq
    rw [fun_apply]
    unfold BindPure.map
    conv => {
      lhs
      rhs
      intro f
      rw  [ law.leftIdentity
          , Function.comp_apply]
    }
    conv => {
      rhs
      rhs
      rw [Function.comp_def]
    }
    -- [done.]

theorem BindPure.seq_assoc.{u, v}
  {T : Type u → Type v} [BindPure T] [law : LawfulBindPure T]
  : ∀ {α β γ : Type u} (Ta : T α) (Tf : T (α → β)) (Tg : T (β → γ)),
    Tg <*> (Tf <*> Ta) = Function.comp <$> Tg <*> Tf <*> Ta
  := by
    intro α β γ Ta Tf Tg
    show seq Tg (fun () => seq Tf (fun () => Ta))
          = seq (seq (map (· ∘ ·) Tg) (fun () => Tf)) (fun () => Ta)
    unfold BindPure.seq BindPure.map
    simp [law.assoc]
    conv => {
      lhs
      rhs ; intro g
      rhs ; intro f
      rhs ; intro a
      rw [law.leftIdentity, Function.comp_apply]
    }
    conv => {
      rhs
      rhs ; ext g
      rw [law.leftIdentity]
      rhs ; ext f
      rw [law.leftIdentity]
      rhs ; ext a
      rw [Function.comp_apply, fun_apply, Function.comp_apply]
    }
    -- [done.]

instance instLawfulApplicativeOfLawfulBindPure.{u, v}
  {T : Type u → Type v} [BindPure T] [LawfulBindPure T]
  : LawfulApplicative T
  where
    map_pure    := BindPure.map_pure
    seqLeft_eq  := BindPure.seqLeft_eq
    seqRight_eq := BindPure.seqRight_eq
    pure_seq    := BindPure.pure_seq
    seq_pure    := BindPure.seq_pure
    seq_assoc   := BindPure.seq_assoc

-- This one wasn't as fun. How do I get the pretty-printer to
--  *not show me `do` blocks???*. If I wanted to see those,
--  I would've enabled such a setting...
