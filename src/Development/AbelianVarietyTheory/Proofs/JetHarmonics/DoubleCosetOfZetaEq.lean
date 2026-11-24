module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem doubleCoset_of_zeta_eq :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g g' : Q.Mx P.k P.r), (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' → (c, g') ∈ Q.DomR P.k P.r Bs.z Bs.z' → P5.zeta P.k P.r Bs.z Bs.z' g = P5.zeta P.k P.r Bs.z Bs.z' g' → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z', g' = h * g * h' := by
  intro Wp Wq _ _ _ _ _ _ P Bs c g g' hg hg' hζ
  obtain ⟨a, ha, b, hb, e⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg.2.1 hg.2.2
  obtain ⟨a', ha', b', hb', e'⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg'.2.1 hg'.2.2
  unfold P5.zeta at hζ
  dsimp only at e e'
  rw [← hζ] at e'
  generalize NF.muZ P.k P.r Bs.μsec (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) = m at e e'
  refine ⟨a' * a⁻¹, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul ha' (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv ha), b⁻¹ * b',
    Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hb) hb', ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul ha
  have h2 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hb
  rw [e', e]
  calc a' * m * b' = a' * (a⁻¹ * a) * m * (b * b⁻¹) * b' := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = a' * a⁻¹ * (a * m * b) * (b⁻¹ * b') := by simp only [Matrix.mul_assoc]

end GlobalTheory.HatNF
