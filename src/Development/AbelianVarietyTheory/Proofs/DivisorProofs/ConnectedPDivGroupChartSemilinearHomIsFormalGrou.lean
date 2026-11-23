module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeriesStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isHom_map_of_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k')
    (hμ : c.IsLawOf μ) (hν : c'.IsLawOf ν) (hφ : ∀ n j, c'.ev n (φ j) = s.app n (c.x n j))
 :
    IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  have hL := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k' e G' c').2 ν hν
  have h2 := GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series p k k' σ d e G G' c c' s φ hφ
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h0 := (GlobalTheory.Katz.counit_dUnit_evA k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h0
    rw [← h0, hφ 0 j, (s.app 0).counit_map, c.aug 0 j, map_zero]
  · let z : ∀ n, G'.A n ⊗[k'] G'.A n := fun n => Coalgebra.comul (R := k') (s.app n (c.x n j))
    have hz : ∀ n, pullbackTwo (G'.res n) (z (n + 1)) = z n := fun n => by
      simp only [z]
      rw [pullTwo_comul, s.res_app, c.res]
    have hl : ∀ n, c'.ev₂ n (subst ν (φ j)) = z n := fun n => by
      rw [(hL.2 n (φ j)).1, hφ n j]
    have hr : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ (μ j))) = z n := fun n => by
      rw [h2 n (μ j), hμ n j, SemiBialgHom.two_comul]
    exact ((GlobalTheory.T.chart_square_coordinates_present_levels p k' e G' c').2 z hz).unique hl hr

end GlobalTheory.Katz
