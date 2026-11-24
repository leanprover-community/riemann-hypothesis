module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

theorem GlobalTheory.TorCls.centraliser_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c :=
  fun p _ G β hβ y₀ c hc => GlobalTheory.TorCls.AtP.atp_of_bijective G (GlobalTheory.T.padicPoints_similitude_GL_product_bijective p G) β hβ y₀ c hc
