module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.BasisEApply
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaC

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem mem_of_isIntegral_fp (L : LocAt F E sig p) {s : L.Fp} (hs : IsIntegral 𝒪[L.Fp] s) : s ∈ 𝒪[L.Fp] := by
  exact (Valuation.integer.integers (ValuativeRel.valuation L.Fp)).mem_of_integral hs

theorem trace_mem (L : LocAt F E sig p) {y : L.Ep} (hy : y ∈ L.O) : Algebra.trace L.Fp L.Ep y ∈ 𝒪[L.Fp] := by
  haveI := L.free
  haveI := PI.ProdFormulaE.Base.finite L
  let b : Module.Basis (Fin 2) L.Fp L.Ep := Module.finBasisOfFinrankEq L.Fp L.Ep L.rank
  exact mem_of_isIntegral_fp L (DeltaB.trace_isIntegral_rank2 b ((L.O_def y).mp hy))

end PI.UnitaryGroupMassFormula.CntFormula.DeltaC
