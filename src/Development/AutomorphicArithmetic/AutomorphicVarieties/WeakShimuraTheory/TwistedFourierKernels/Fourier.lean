module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.fourier :
    ∀ (K Q : Type) [Field K] [IsAlgClosed K] [CharZero K] [CommGroup Q] [Finite Q] (a : MonoidAlgebra K Q), (∀ χ : Q →* Kˣ, MonoidAlgebra.lift K K Q ((Units.coeHom K).comp χ) a = 0) → a = 0 := by
  intro K Q _ _ _ _ _ a h
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent Q : ℕ) : K) := ⟨by exact_mod_cast NeZero.ne (Monoid.exponent Q)⟩
  let ev : Q → ((Q →* Kˣ) →* K) := fun q =>
    { toFun := fun χ => (χ q : K), map_one' := by simp, map_mul' := fun x y => by simp }
  have hinj : Function.Injective ev := by
    intro q q' hq
    refine (CommGroup.forall_apply_eq_apply_iff Q (M := K)).1 fun φ => ?_
    exact Units.ext (DFunLike.congr_fun hq φ)
  have hli := (linearIndependent_monoidHom (Q →* Kˣ) K).comp ev hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun q => a.coeff q) (by
    funext χ
    have := h χ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [ev, Finset.sum_apply] using this)
  ext q
  simpa using key q
