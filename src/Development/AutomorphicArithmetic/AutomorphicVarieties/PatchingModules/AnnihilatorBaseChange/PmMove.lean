module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaSuppBc
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmMove :
    ∀ (BB MM B B' : Type) [CommRing BB] [IsNoetherianRing BB] [AddCommGroup MM] [Module BB MM] [Module.Finite BB MM] [CommRing B] [Algebra BB B] [CommRing B'] [IsLocalRing B'] [Algebra BB B'] (p' : Ideal BB) (Z : Ideal B), IsCplAt BB p' B' → Z.IsPrime → Module.annihilator B (B ⊗[BB] MM) ≤ Z → Z.comap (algebraMap BB B) ≤ p' → ∃ Z' : Ideal B', Z'.IsPrime ∧ Module.annihilator B' (B' ⊗[BB] MM) ≤ Z' ∧ Z'.comap (algebraMap BB B') = Z.comap (algebraMap BB B) := by
  intro BB MM B B' _ _ _ _ _ _ _ _ _ _ p' Z hB' hZ hann hle
  haveI := hZ
  obtain ⟨Q, hQ, hQc⟩ := (IsCplAt.exists_prime_over BB p' B' hB').1 _ (Ideal.IsPrime.comap _) hle
  refine ⟨Q, hQ, ?_, hQc⟩
  let zP : PrimeSpectrum B := ⟨Z, hZ⟩
  let qP : PrimeSpectrum B' := ⟨Q, hQ⟩
  have hz : zP ∈ Module.support B (B ⊗[BB] MM) := Module.mem_support_iff_of_finite.mpr hann
  have hz' := (mem_support_baseChange BB B MM zP).mp hz
  have heq : PrimeSpectrum.comap (algebraMap BB B') qP = PrimeSpectrum.comap (algebraMap BB B) zP :=
    PrimeSpectrum.ext hQc
  have hq : qP ∈ Module.support B' (B' ⊗[BB] MM) := by
    rw [mem_support_baseChange, heq]
    exact hz'
  exact Module.mem_support_iff_of_finite.mp hq
