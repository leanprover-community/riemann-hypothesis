module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSplit
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem TwistVanishAll.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanishAll.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun i b c hi hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c i
  have := hc₀ i hi c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
