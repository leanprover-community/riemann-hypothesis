module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd

private theorem finOrd_kills {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 1 ≤ M) {φ : G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) : IsOfFinOrder φ := by
  have ho : IsOpen (φ.ker : Set (G F Ω)) := by
    have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
      classical
      refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
      simpa [Polynomial.mem_nthRoots hM] using hζ
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds ?_) fun s hs => ?_)
    · simp only [Set.mem_iInter]
      exact fun ζ _ => Subgroup.one_mem _
    · simp only [Set.mem_iInter] at hs
      exact hφ s fun ζ hζ => hs ζ hζ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨_, hpos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  exact φ.ker.pow_index_mem s
