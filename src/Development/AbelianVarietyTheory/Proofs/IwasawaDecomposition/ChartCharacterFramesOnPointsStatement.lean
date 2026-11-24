module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Formalism.LocalToGlobal.Columns.TwQExact
public import Formalism.LocalToGlobal.Columns.TwQLev
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartCharacterFramesOnPoints
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartCharacter_frames_onPoints : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q), g ∈ UAd hc n → ∀ (κ : FrmG Λ Θ), ufGL X.E n κ.1 = 1 → FrExact q g r.1.1 → FrExact q (g * z.1) (ya Λ Θ κ r).1.1 → ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.chr_frames | exact GlobalTheory.Mem.Col2.ChEx.chr_frames | (intros; apply GlobalTheory.Mem.Col2.ChEx.chr_frames <;> assumption)
