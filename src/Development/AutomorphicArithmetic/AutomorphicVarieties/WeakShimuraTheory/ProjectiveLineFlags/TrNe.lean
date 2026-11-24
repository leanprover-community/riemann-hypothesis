module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.trNe :
    ∀ {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H : Subgroup Γ) (χ : Fin (n + 1) → Γ →* kˣ), (Function.Injective fun i => (χ i).comp H.subtype) →
          H = ⊤ ∨ ∃ g, g ∉ H ∧ ∑ i, (χ i g : k) ≠ 0 := by
  intro Γ k _ _ n H χ hinj
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hH, hz⟩ := hcon
  have hz' : ∀ g, g ∉ H → ∑ i, (χ i g : k) = 0 := by
    intro g hg
    by_contra h
    exact hz ⟨g, hg, h⟩
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 ∉ H := by
    by_contra h
    apply hH
    rw [eq_top_iff]
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  let ψ : Fin (n + 1) → (H →* k) := fun i => (Units.coeHom k).comp ((χ i).comp H.subtype)
  have hψ : Function.Injective ψ := by
    intro i j hij
    apply hinj
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom H k).comp ψ hψ
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (fun i => (χ i g0 : k)) (by
    funext h
    have hm : g0 * (h : Γ) ∉ H := fun hm => hg0 ((H.mul_mem_cancel_right h.2).1 hm)
    have := hz' _ hm
    simp only [map_mul, Units.val_mul] at this
    simpa [ψ, Finset.sum_apply] using this) 0
  exact (χ 0 g0).ne_zero h0
