module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
public import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsCuspFormFourClausesExplicitConstant
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

theorem _root_.GlobalTheory.T.exists_cuspForm_four_clauses_explicitConstant : ∀ (D : D7) (T : Top D) (h : LawsP T) (DF q : ℕ) (R0 P tableLineDegreeTwo : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → (∀ j, InR D j → p16 D.host.E D.R.r q D.R.m 5 (max 1 (Fintype.card (T.U j T.σ₀).Comp) * 5 ^ (8 * I2.PT.f D.host.E * D.R.r ^ 2)) ≤ min P tableLineDegreeTwo) → 0 ≤ P → ETEx h P (EtArch h (I2.th (E := D.host.E) q R0) tableLineDegreeTwo) := by
  first | exact @GlobalTheory.EtaAn.exists_form_four_clauses | exact GlobalTheory.EtaAn.exists_form_four_clauses | (intros; apply GlobalTheory.EtaAn.exists_form_four_clauses <;> assumption)
