module

public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.block_ext_mem_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  first | exact @GlobalTheory.TopStep.ext_mem_twisted_k1_level | exact GlobalTheory.TopStep.ext_mem_twisted_k1_level | (intros; apply GlobalTheory.TopStep.ext_mem_twisted_k1_level <;> assumption)
