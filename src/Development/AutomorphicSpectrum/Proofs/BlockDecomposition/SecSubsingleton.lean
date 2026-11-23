module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwZeroGen

theorem sec_subsingleton (hLc : LcCover) (V : Scheme.{0}) [IsEmpty V] {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton (Sec G V) := by
  let f : LocallyConstant V Empty :=
    ⟨isEmptyElim, fun s => by rw [Set.eq_empty_of_isEmpty (isEmptyElim ⁻¹' s)]; exact isOpen_empty⟩
  obtain ⟨W, j, -, -, -, hG⟩ := hLc V Empty f
  constructor
  intro a b
  exact (hG R G (fun e => e.elim)).unique (fun e => e.elim) (fun e => e.elim)

private theorem twGen_zero_eq_of_eq_pow {q : ℕ} {V : Scheme.{0}} (η θ : Prim q ↑(V.presheaf.obj (op ⊤)))
    (b : (ZMod q)ˣ) (h : η.1 = θ.1 ^ (b : ZMod q).val) : twGen 0 η = twGen 0 θ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨θ, η, b, h, ?_⟩)
  rw [zpow_zero]
  rfl

theorem twZero : RootPow → LcCover → RepRoot → TwZero := by
  intro hR hL hP hIn q _ U ζ ξ
  obtain ⟨f, hf, hu⟩ := (hR q U ζ).2 ξ
  obtain ⟨W, j, hWf, -, -, hG⟩ := hL U (ZMod q) f
  have key : ∀ a, Sec.res (j a) (twGen 0 ζ) = Sec.res (j a) (twGen 0 ξ) := by
    intro a
    rw [((hP q 0 U ζ).1 (W a) (j a)).1, ((hP q 0 U ξ).1 (W a) (j a)).1]
    by_cases ha : IsUnit a
    · symm
      apply twGen_zero_eq_of_eq_pow _ _ ha.unit
      have hpw := hf (W a) (j a) a (hWf a)
      have e : (primRes (j a) ξ).1 = (CommRingCat.Hom.hom (Scheme.Hom.appTop (j a))) ξ.1 := rfl
      rw [IsUnit.unit_spec, e]
      exact hpw
    · haveI : IsEmpty (W a) := ⟨fun v => by
        have hv := hu (j a v)
        rw [hWf a v] at hv
        exact ha hv⟩
      exact (sec_subsingleton hL (W a) (tw q 0)).elim _ _
  obtain ⟨y, -, hy⟩ := hG (ZMod q) (tw q 0) (fun a => Sec.res (j a) (twGen 0 ζ))
  exact (hy _ (fun a => rfl)).trans (hy _ (fun a => (key a).symm)).symm

end GlobalTheory.CompanionTheory.TwZeroGen
