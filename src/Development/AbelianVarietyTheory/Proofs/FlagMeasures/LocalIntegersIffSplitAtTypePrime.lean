module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
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

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem intV_iff_sp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp), (∀ i, (gp i).Prime) → (∀ i, SplitsIn E (gp i)) → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : E ⊗[F] v.adicCompletion F), x ∈ intV E v ↔ (G.sp i v hv x).1 ∈ v.adicCompletionIntegers F ∧ (G.sp i v hv x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm gp G _ _ i v hv x
  exact split_integral_local F E v (G.sp i v hv) (G.sp_alg i v hv) x

end GlobalTheory.St.G
