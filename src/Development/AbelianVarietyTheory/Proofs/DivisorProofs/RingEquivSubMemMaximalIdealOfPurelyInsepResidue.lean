module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResFix

theorem sigma_fix_mod_max : ∀ (A R R' : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (b : A →+* R) (θ : R →+* R') [IsLocalHom θ] (q : ℕ) [ExpChar (ResidueField R) q] (σ : R' ≃+* R'), (∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a)) → (∀ a, σ (θ (b a)) = θ (b a)) → ∀ r, σ (θ r) - θ r ∈ maximalIdeal R' := by
  intro A R R' _ _ _ _ _ b θ _ q _ σ hins hfix r
  obtain ⟨n, a, ha⟩ := hins (residue R r)
  have h1 : r ^ q ^ n - b a ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_pow, ha, sub_self]
  have h2 : θ r ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit θ _ h1
    simpa [map_sub, map_pow] using this
  have h3 : σ (θ r) ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit (σ : R' →+* R') _ h2
    simpa [map_sub, map_pow, hfix a] using this
  haveI : ExpChar (ResidueField R') q :=
    expChar_of_injective_ringHom (ResidueField.map θ).injective q
  have e2 : residue R' (θ r) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h2
  have e3 : residue R' (σ (θ r)) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h3
  have e4 : (residue R' (σ (θ r)) - residue R' (θ r)) ^ q ^ n = 0 := by
    rw [sub_pow_expChar_pow, e2, e3, sub_self]
  rw [← residue_eq_zero_iff, map_sub]
  exact pow_eq_zero_iff (pow_ne_zero _ (expChar_pos (ResidueField R') q).ne') |>.mp e4

end GlobalTheory.ResFix
