module

public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSmallCoeffEtaValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.KeyHol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_sec_rdU_ne_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (x₀ : Frame (U.X k).Ψ r)
    (hx₀ : x₀ ∈ (U.X k).dom) :
    ∃ (m : ℕ) (f : Rul Xo c), f ∈ sec Xo c 0 (2 * (m + 1)) ∧ Formalism.L2.PjFree.rdU U f k x₀ ≠ 0 := by
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by norm_num
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (GlobalTheory.EtaForm.LatMod Dw 3) := Fintype.ofFinite _
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => U.un k ⟨x₀, hx₀⟩)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → GlobalTheory.EtaForm.LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (GlobalTheory.EtaForm.shiftFam 3 0)
  have hpos : 0 < Nat.card (GlobalTheory.EtaForm.LevGrp Dw (3 ^ 4)) := Nat.card_pos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  refine ⟨m, f, by have := hsec f hrule; rwa [hm] at this, ?_⟩
  have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) (U.un k ⟨x₀, hx₀⟩)
    (hT _ _)).1
  have h0 := hne 0 _ hv
  have e1 : Formalism.L2.PjFree.rdU U f k x₀ = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x₀, hx₀⟩)) := dif_pos hx₀
  rw [e1]
  exact h0

end GlobalTheory.CuspFrom.KeyHol
