module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.ContraPair
open GlobalTheory.ThetaPull (cFin pInf_conjAd pFin_conjAd conjAd_conjAd continuous_conjAd)
open scoped ContDiff

namespace GlobalTheory.BarPull

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

theorem map_map_comm (p : R →+* S) (c : R →+* R) (c' : S →+* S) (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) := by
  ext i j
  exact h _

theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R) (h : Continuous c) :
    Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))

theorem map_unip {r : ℕ} (c : R →+* R) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) := by
  ext i j
  change c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) R) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

end GlobalTheory.BarPull

end
