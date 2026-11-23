module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatFormM
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RootEx
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.locNorm : UpperTheory.V.Z.Sym.Loc.LocNorm := by
  rintro O K _ _ _ _ _ Δ τ L ⟨τ₀, e₀⟩
  by_cases h1 : IsUnit (2 + τ₀)
  · obtain ⟨lam, -, hl⟩ := normEx O K Δ L h1.unit
    have ep : algebraMap O K (2 + τ₀) = 2 + τ := by simp [map_ofNat, e₀]
    rw [IsUnit.unit_spec, ep] at hl
    have h0 : 2 + τ ≠ 0 := ep ▸ (h1.map _).ne_zero
    have hll : lam * star lam = algebraMap K _ (2 + τ) := by rw [← hl, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    refine ⟨lam • ofE Δ ((2 + τ)⁻¹ • (1 + ω : Etau K τ)), ?_⟩
    have s1 : ∀ x : Etau K τ, sigL (lam • ofE Δ x) = star lam • ofE Δ x := fun x => by ext <;> simp [sigL, ofE]
    rw [s1, smul_mul_smul_comm, hll]
    ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  · obtain ⟨x, y, -, hu, hn⟩ := rootEx O K Δ τ L τ₀ (-1) e₀ (by simpa [add_comm] using h1)
    obtain ⟨ν, -, hν⟩ := normEx O K Δ L (-1)
    exact ⟨_, (datFormM O K Δ τ L 1 _ (by simpa using hu) hn ν (by simpa using hν) 1 one_ne_zero).1⟩
