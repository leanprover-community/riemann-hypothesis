module

public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Mathlib.RingTheory.Frobenius
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cheb :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (σ : Gal(L/K)) (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite → ∃ v ∉ T, ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ IsArithFrobAt (𝓞 K) σ w.asIdeal := by
  intro K L _ _ _ _ _ _ σ T hT
  classical
  let C : Set Gal(L/K) := {τ | IsConj σ τ}
  have hCc : ∀ a ∈ C, ∀ τ : Gal(L/K), τ * a * τ⁻¹ ∈ C := by
    intro a ha τ
    exact IsConj.trans ha (isConj_iff.mpr ⟨τ, rfl⟩)
  have hD := GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := K) (L := L) C hCc
  have hpos : (0 : ℝ) < (Nat.card C : ℝ) / Nat.card Gal(L/K) := by
    have : Nonempty C := ⟨⟨σ, IsConj.refl σ⟩⟩
    apply div_pos
    · exact_mod_cast Nat.card_pos
    · exact_mod_cast Nat.card_pos
  have key : ∀ S : Set (HeightOneSpectrum (𝓞 K)),
      Set.HasDirichletDensity S ((Nat.card C : ℝ) / Nat.card Gal(L/K)) → (S \ T).Nonempty := by
    intro S hS
    refine Set.Infinite.nonempty (Set.Infinite.diff ?_ hT)
    intro hfin
    have h0 := GroundTheory.Global.hasDirichletDensity_zero_of_finite hfin
    exact hpos.ne' (hS.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq)
  obtain ⟨v, ⟨hram, w, hwv, hfw⟩, hvT⟩ := key _ hD
  obtain ⟨c, hc⟩ := isConj_iff.mp hfw
  have hne : c⁻¹ • w.asIdeal ≠ ⊥ := by
    intro h
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 L) => c • I) h
    simpa using this
  let w' : HeightOneSpectrum (𝓞 L) := ⟨c⁻¹ • w.asIdeal, Ideal.IsPrime.smul c⁻¹, hne⟩
  have hw'v : w'.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.smul c⁻¹
  refine ⟨v, hvT, w', hw'v, (hram w' hw'v), ?_⟩
  have hF := (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal).conj c⁻¹
  rw [← hc] at hF
  have e : c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ := by group
  rw [e] at hF
  exact hF
