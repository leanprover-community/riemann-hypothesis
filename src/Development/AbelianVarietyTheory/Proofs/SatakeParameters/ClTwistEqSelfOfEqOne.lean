module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory

open GlobalTheory.SmGL GlobalTheory.LocGL in
private theorem clTwist_eq_self_of_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) (h1 : χ = 1) : clTwist c χ hχ = c := by
  subst h1; exact clTwist_one c hχ

theorem rankOne_algNorm_locComp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (π : CuspSub E 1)
    (ψ : HChar E) (hπ : CG.mk π = CG.ofChar ψ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin 1) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    algNorm σ = IrrGL.ofChar (ψ.loc w) (ParLaws.isSmoothChar_loc ψ w) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [hπ] at h1
  have h2 := CG.IsLoc.unique E 1 _ w _ _ h1 (CG.isLoc_ofChar ψ w)
  obtain ⟨e⟩ := Quotient.exact h2
  unfold algNorm IrrGL.nu IrrGL.tw IrrGL.of IrrGL.ofChar
  congr 1
  refine (clTwist_eq_self_of_eq_one _ _ _ ?_).trans ?_
  · ext g
    simp [GlobalTheory.SmGL.detChar, GlobalTheory.SmGL.absPow]
  apply Quotient.sound
  exact ⟨e.trans (Representation.Equiv.refl _)⟩

end GlobalTheory
