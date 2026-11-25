module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.mem_framedLevel_iff_two_adelic_points : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') := by
  exact @GlobalTheory.Mem.Col2.TopCh.mem_topU_iff
