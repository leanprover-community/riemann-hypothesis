module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocyclesStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.isRigOf_rigMk : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  intro p k _ d G c μ ρ hμ hρ
  have hcoc := GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ
  have hdu := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  have hom := GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c
  have hone := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hpres := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2
  constructor
  · intro v
    obtain ⟨⟨z, u⟩, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨s, hs, -⟩ := hpres z.1 (fun n => (z.2 n).2)
    obtain ⟨w, hw, -⟩ := hom.2 u
    have hz : (fun n => c.ev₂ n s) = z.1 := funext hs
    refine ⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩
    exact hρ s w z u (fun n => (hs n).symm) hw
  · intro s w hs
    let z : G.cocycles := ⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩
    let u : G.omega := ⟨fun n => ∑ i, w i • dUnit (R := k) (c.x n i), hom.1 w⟩
    rw [hρ s w z u (fun _ => rfl) (fun _ => rfl)]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨B, hB⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq] at hB
      obtain ⟨b, hb, -⟩ := hone.2.2 B.1 B.2
      refine ⟨b, ?_, ?_⟩
      · have hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s := fun n => hone.2.1 n s
        obtain ⟨t, -, ht⟩ := hpres (fun n => c.ev₂ n s) hz2
        have h1 := ht s (fun _ => rfl)
        have h2 := ht (cob1 μ b) (fun n => by
          rw [(hlaw n b).2, hb n]
          exact (congrArg (fun y : G.cocycles => y.1 n) hB.1))
        exact h1.trans h2.symm
      · obtain ⟨w', -, hw'⟩ := hom.2 u
        have e1 := hw' w (fun _ => rfl)
        have e2 := hw' (lin b) (fun n => by
          rw [← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]
          change _ = dUnit (R := k) (c.ev n b)
          rw [hb n]
          exact (congrArg (fun y : G.omega => y.1 n) hB.2).symm)
        exact e1.trans e2.symm
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq]
      constructor
      · apply Subtype.ext; funext n
        exact ((hlaw n b).2).symm
      · apply Subtype.ext; funext n
        exact (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2
