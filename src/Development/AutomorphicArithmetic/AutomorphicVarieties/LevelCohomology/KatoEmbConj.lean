module

public import Formalism.ConjugateSelfDual.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.Algebra.Hom.Rat
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.embConj :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (j₀ : Ω →+* Om l) (τ : K →+* Om l), ∃ g : G ℚ Ω, (j₀.comp (g : Ω →+* Ω)).comp (algebraMap K Ω) = τ := by
  intro l _ K Ω _ _ _ _ _ _ _ j₀ τ
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hsub : ∀ x : K, ∃ b : Ω, j₀ b = τ x := by
    intro x
    have hp : minpoly ℚ x ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
    have hrat : j₀.comp (algebraMap ℚ Ω) = τ.comp (algebraMap ℚ K) := Subsingleton.elim _ _
    have hroot : τ x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j₀).roots := by
      rw [Polynomial.map_map, Polynomial.mem_roots_map hp, hrat, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    rw [(IsAlgClosed.splits ((minpoly ℚ x).map (algebraMap ℚ Ω))).roots_map j₀] at hroot
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hroot
    exact ⟨b, hb⟩
  choose f hf using hsub
  let τ' : K →+* Ω :=
    { toFun := f
      map_one' := j₀.injective (by rw [hf, map_one, map_one])
      map_mul' := fun a b => j₀.injective (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := j₀.injective (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => j₀.injective (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let g0 : Ω →ₐ[ℚ] Ω := (τ'.toRatAlgHom).liftNormal Ω
  refine ⟨AlgEquiv.ofBijective g0 (Algebra.IsAlgebraic.algHom_bijective g0), ?_⟩
  ext x
  show j₀ (g0 (algebraMap K Ω x)) = τ x
  rw [AlgHom.liftNormal_commutes]
  exact hf x
