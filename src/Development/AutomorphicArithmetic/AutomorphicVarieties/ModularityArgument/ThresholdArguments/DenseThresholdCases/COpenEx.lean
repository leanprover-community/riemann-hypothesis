module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.DimOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameConditionAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.J
open UpperTheory.V.Pr
theorem mod_l_open_existence
    {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {c : Coef l}
    [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} (H : LinkHyp c N e η σ B M)
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
    {k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ} (v : Φ.V)
    {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
    {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (Λ : W.LamObj R.r)
    (hΛ : Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin (n * Module.finrank ℚ (W.Lp L))) c₁.O))
    (J : Ideal R.B₀.B) (hJ : R.B₀.ModularAlt ι J Λ) (hs : R.T.IdealSpecializationPoint J) : R.T.ModIn J := by
  obtain ⟨hd, -⟩ := degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v
  refine ⟨⟨Λ, hJ.ring.fin⟩, ?_, fun g hg => (hJ.ring.unr0 R.v0 g hg).1,
    n4Of Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f n ka R, hJ.p1, hJ.p3, hs⟩
  intro Z hZ
  haveI : IsDiscreteValuationRing c₁.O := c₁.dvr
  have := dimOf c₁.O Λ.Λ R.B₀.B (Λ.toPair R.B₀.u : Λ.Λ →+* R.B₀.B) J _ hΛ hJ.ring.fin hJ.ring.tf Z hZ
  rw [← hd] at this
  exact this
end UpperTheory.V.J
end
