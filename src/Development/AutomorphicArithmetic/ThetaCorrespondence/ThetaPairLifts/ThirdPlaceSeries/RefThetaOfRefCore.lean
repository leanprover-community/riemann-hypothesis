module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSecOfMemCuspWWtZ
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuoShapeStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem

@[expose] public section



section
set_option autoImplicit false

noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum
theorem refTheta_of_refCore_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.ReferenceCore → _root_.GlobalTheory.RefSum.ReferenceTheta := by
  intro hS hR
  have hW := _root_.GlobalTheory.T.quotient_weight_gap_bounds' hS
  refine Closed.imp (Closed.and hR hW) ?_
  intro eps Fm CH inst H
  obtain ⟨⟨C, hC, a, h⟩, _, _, b, h'⟩ := H
  refine ⟨C, hC, max a b, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨S, e, s, hPS, hT, hq⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp i hi u1 hu
  have hD := (h' x hx ((le_max_right _ _).trans hle) ι p hp i hi u1 hu).2.2.2.2.2.2.1
  refine ⟨S, e, s, hPS, hT, fun q hq' => le_trans ?_ (hq q hq')⟩
  exact refExp_vp_cover_le _ p.T _ Y _ _ p.fw.laws ⟨by omega, by omega⟩ hY.1 _ _ hD _ q hq'
end GlobalTheory.RefSum
end
end
