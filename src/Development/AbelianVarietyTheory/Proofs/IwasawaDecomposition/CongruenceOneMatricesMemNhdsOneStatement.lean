module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruenceOneMatricesMemNhdsOne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev


theorem _root_.GlobalTheory.T.congruenceOne_matrices_mem_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ N ∈ nhds (1 : GL (Fin n) (AfE F E)), ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → 0 < m →
      ∀ k : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k → GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k⁻¹ → k ∈ N := by
  first | exact @GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | exact GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | (intros; apply GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds <;> assumption)
