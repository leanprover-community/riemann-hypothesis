module

public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.KummerTheory.TwSecPfGamma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PrimTors : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], SH B → IsUnit (q : B) →
  Nonempty (Prim q B) ∧ ∀ (i : ℤ) (ζ : Prim q B), Function.Bijective fun t : ZMod q =>
    (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q i B)

def SecSH : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (R : Type) [CommRing R]
  (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), Function.Bijective (ofRings.sec (R := R) M (Spec (CommRingCat.of A)))

theorem TwSec_of (h1 : PrimTors) (h2 : SecSH) : TwSec := by
  intro q _ A _ hA hq
  have hB := SHGamma_holds A hA
  have hqB : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨hne, hbij⟩ := h1 q _ hB hqB
  refine ⟨hne, fun i ζ => ?_⟩
  have key : (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) =
      ofRings.sec (R := ZMod q) (twF q i) (Spec (CommRingCat.of A)) ∘ (fun t : ZMod q =>
        (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
          (Prim q _ →₀ ULift.{1} (ZMod q)) ⧸ twRel q i _)) := by
    funext t
    simp only [twGen, ofRings.sec]
    exact (map_smul _ _ _).symm
  rw [key]
  exact (h2 A hA (ZMod q) (twF q i)).comp (hbij i ζ)

end LateralTheory.KummerTheory
