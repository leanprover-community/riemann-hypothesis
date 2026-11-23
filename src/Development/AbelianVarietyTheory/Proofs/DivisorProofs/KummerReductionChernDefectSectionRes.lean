module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
