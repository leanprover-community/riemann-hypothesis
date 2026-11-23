module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFrames
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  first | exact @GlobalTheory.FlagGS.gram_schmidt_frames | exact GlobalTheory.FlagGS.gram_schmidt_frames | (intros; apply GlobalTheory.FlagGS.gram_schmidt_frames <;> assumption)
