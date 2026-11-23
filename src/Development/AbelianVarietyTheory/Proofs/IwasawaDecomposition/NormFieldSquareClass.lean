module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicDivOfBeta
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem nfSq_of_fieldDat : GlobalTheory.NormSum.IntSt → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.BotSmall → NFSq := by
  intro hI hFD hTE hBS
  obtain ⟨CF0, h⟩ := GlobalTheory.SqTop.SqField.gBig_and hFD (GlobalTheory.SqTop.SqField.gBig_and hTE hBS)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ he hx hR T L μ₀ hμ G => ?_⟩
  obtain ⟨⟨_, _, _, _, hΛ⟩, hT, hQ, -, hB⟩ := h C0 le_rfl D large₂ he hx hR T L μ₀ hμ G
  exact GlobalTheory.SqTop.SqField.sqIn_of G μ₀ hI hΛ
    (fun i j s h1 h2 c => let ⟨x, a, b, _, d⟩ := hT i j s h1 h2 c; ⟨x, a, b, d⟩) hQ hB

end GlobalTheory.Mem.LiteralAutomorphy

end
