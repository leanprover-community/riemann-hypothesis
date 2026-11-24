module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.CardQuotientEqAbsNorm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ModFIotaFinitePlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormIndex
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

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE

theorem normLoc_of (hI : IndexFormula) (hC : CardStep) : St.NormLoc :=
  fun _F _ _ p _K _ _ _ _ ι hd hv z => modF_iota_finitePlace p ι hI hC hd hv z

theorem normLoc_of_card (hC : CardStep) : St.NormLoc := normLoc_of modulus_mul_card_quotient hC

theorem modulus_eq_finitePlace : St.NormLoc := normLoc_of_card card_quotient_eq_absNorm

theorem modF_localization_eq_adicAbv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) [IsNonarchimedeanLocalField L.Fp] (z : F) :
    modF L.Fp (L.ιF z) = NumberField.HeightOneSpectrum.adicAbv F p z :=
  modF_locAt modulus_mul_card_quotient card_quotient_eq_absNorm L z

end PI.ProdFormulaE
