module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetEx

theorem exists_finset_sdLat_reps : ∀ (X : Fields), X.Ok → ∀ n : ℕ, ∃ T : Finset (Submodule (𝓞 X.E) (Sp X.E n)), (∀ N ∈ T, IsSdLat N) ∧ ∀ N : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat N → ∃ N₀ ∈ T, ∃ γ : UF X.E n, N = gmap γ.1 N₀ := by
  intro X hX n
  obtain ⟨s, hs, H⟩ := unimod_finite (E := X.E) (posStar_of_conj hX.conjE) n
  refine ⟨s, hs, fun N hN => ?_⟩
  obtain ⟨N₀, h₀, g, hg, e⟩ := H N hN.1 hN.2
  exact ⟨N₀, h₀, ⟨g, hg⟩, e.symm⟩

end GlobalTheory.Mem.Col2.JetEx
