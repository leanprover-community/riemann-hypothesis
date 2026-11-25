module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.finitePart_preserves_form_det_norm_one : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  first | exact @GlobalTheory.Member.finHom_herm_det
