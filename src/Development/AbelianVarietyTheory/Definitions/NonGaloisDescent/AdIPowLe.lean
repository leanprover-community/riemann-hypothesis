module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal

namespace GlobalTheory.BSP

section Cover

variable {l : ℕ} {R : Type} [CommRing R]

abbrev adI (B : Obj l R) : Ideal B.A := Ideal.span {(l : B.A)} ⊔ B.I

theorem adI_pow_le {B B' : Obj l R} (f : Hom B B') (m : ℕ) : adI B ^ m ≤ (adI B' ^ m).comap f.f := by
  refine le_trans (Ideal.pow_right_mono ?_ m) (Ideal.le_comap_pow f.f m)
  refine sup_le ?_ fun a ha => Ideal.mem_sup_right (f.f_I a ha)
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

def qmap {B B' : Obj l R} (f : Hom B B') (m : ℕ) : (B.A ⧸ adI B ^ m) →+* (B'.A ⧸ adI B' ^ m) :=
  Ideal.quotientMap _ f.f (adI_pow_le f m)

theorem qmap_mk {B B' : Obj l R} (f : Hom B B') (m : ℕ) (a : B.A) :
    qmap f m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f.f a) := rfl

structure IsPO {B C B' C' : Obj l R} (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C') : Prop where
  comm : k'.comp h = h'.comp k
  po : ∀ m : ℕ, CategoryTheory.IsPushout (CommRingCat.ofHom (qmap h m)) (CommRingCat.ofHom (qmap k m))
    (CommRingCat.ofHom (qmap k' m)) (CommRingCat.ofHom (qmap h' m))

structure Stable {B C : Obj l R} (h : Hom B C) : Prop where
  flat : ∀ m : ℕ, (qmap h m).Flat
  po : ∀ (B' : Obj l R) (k : Hom B B'), ∃ (C' : Obj l R) (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h'

structure Cover {B C : Obj l R} (h : Hom B C) : Prop where
  stable : Stable h
  ff : ∀ m : ℕ, (qmap h m).FaithfullyFlat

structure IsLoc {B C : Obj l R} (s : B.A) (h : Hom B C) : Prop where
  away : ∀ m : ℕ, letI := (qmap h m).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (adI B ^ m) s) (C.A ⧸ adI C ^ m)
  univ : ∀ (Q : Obj l R) (a : Hom B Q), IsUnit (a.f s) → ∃ c : Hom C Q, c.comp h = a

end Cover

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

structure Eval (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] where
  fin : Module.Finite B.A N
  proj : Module.Projective B.A N

  v : ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q), Hom bk.prism Q → N →ₛₗ[a.f] (Fin d → Q.A)
  bc : ∀ {Q} (a : Hom B Q) (g : Hom bk.prism Q), SemiBC (v a g)
  v_ε : ∀ {Q} (a : Hom B Q) (g g' : Hom bk.prism Q) (x : N), v a g x = (S.ε g g').mulVec (v a g' x)
  v_nat : ∀ {Q Q'} (c : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) (i : Fin d),
    v (c.comp a) (c.comp g) x i = c.f (v a g x i)

def IsPsi {S : Strat bk d} {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (Ψ : N →ₛₗ[B.D.φ] N) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
    BK.hf g bk.E ^ S.a • V.v a g (Ψ x) =
      a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)

def IsCoord {S : Strat bk d} {M : FCrys l ↥(OL K)} (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism))
    {B : Obj l ↥(OL K)} (V : Eval S B (M.M B)) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B),
    M.tr a x = ∑ i, V.v a g x i • M.tr g (e i)

end GlobalTheory.BSP
