module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct ValuativeRel

namespace GlobalTheory.CompanionTheory.IwahoriDatumGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

theorem fact_up' {x : GL (Fin n) k} (hx : x ∈ iwahori k (Fin n)) :
    ∃ c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n), ∃ b ∈ iwahori k (Fin n) ⊓ (diagT k (Fin n)).range,
      ∃ a ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n), x = c * b * a := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hx
  exact ⟨u, ⟨(GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu, hu.1⟩, _,
    ⟨diagT_mem_iwahori hd, ⟨d, rfl⟩⟩, c, ⟨KOne_le_iwahori k (Fin n) hc.2, hc.1⟩, rfl⟩

end GlobalTheory.CompanionTheory.IwahoriDatumGL

end
