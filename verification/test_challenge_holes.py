"""Bounded negative controls for the exact comparator Challenge-hole exception."""
import copy,hashlib,json,sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'scripts'))
from check_release import ROOT,check_challenge_config,check_challenge_text,check_proof_tokens,load_challenges
BASE='module\nnamespace Test\ntheorem result : True := by\n  sorry\nend Test\n'
class ChallengeHoles(unittest.TestCase):
 def test_compared_terminal_hole(self):check_proof_tokens('Challenge.lean',BASE,['Test.result'])
 def test_production_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('DirectedDistances/Example.lean',BASE)
 def test_solution_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('Palomar/Pilot/Solution.lean',BASE)
 def test_extra_tactic_before_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  skip\n  sorry'),['Test.result'])
 def test_extra_tactic_after_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  sorry\n  trivial'),['Test.result'])
 def test_noncompared_declaration_hole_rejected(self):
  text=BASE.replace('end Test','theorem extra : True := by sorry\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_renamed_declaration_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('result :','different :'),['Test.result'])
 def test_nested_comment_is_masked(self):
  check_challenge_text(BASE.replace('  sorry','  /- sorry /- admit -/ -/ sorry'),['Test.result'])
 def test_admit_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE.replace('sorry','admit'),['Test.result'])
 def test_custom_axiom_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE+'axiom bad : False\n',['Test.result'])
 def test_hole_in_noncompared_definition_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE+'def extra : True := by sorry\n',['Test.result'])
 def test_actual_exact_challenges_and_configurations(self):
  specs=load_challenges()
  base={'Palomar/Pilot/Challenge.lean','Palomar/AppendixA/Challenge.lean'}
  self.assertEqual(sum(len(specs[p]['declarations']) for p in base),7)
  self.assertTrue(all(s['declarations'] for s in specs.values()))
 def test_config_name_mismatch_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['theorem_names']=['Test.other']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_extra_kernel_key_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['external_kernels']=[]
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_nanoda_required(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['enable_nanoda']=False
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_proved_public_typing_auxiliary_allowed(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_1']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  check_challenge_config(spec,config)
 def test_typing_auxiliary_is_not_an_extra_hole(self):
  with self.assertRaises(ValueError):
   check_challenge_text(BASE+'theorem DirectedDistances.Example.record._proof_1 : True := by sorry\n',['Test.result'])
 def test_arbitrary_auxiliary_name_rejected(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['Test.unreviewed']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_duplicate_proved_auxiliary_rejected(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  name='DirectedDistances.Example.record._proof_1'
  spec['proved_auxiliaries']=[name,name]
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_definition_holes_remain_forbidden_with_typing_auxiliary(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_1']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  config['definition_names']=['DirectedDistances.Example.data']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_typing_auxiliary_budget_enforced(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_'+str(i) for i in range(13)]
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_named_proved_characterization_allowed_only_in_finite_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['path']='Palomar/Principal/BoltzmannDistances/Challenge.lean'
  spec['declarations']=['DLQG1.Palomar.Principal.boltzmann_distances']
  spec['solution_path']='Palomar/Principal/BoltzmannDistances/Solution.lean'
  spec['proved_auxiliaries']=['DirectedDistances.PlanarMap.mem_sourceSinkPathLengthsBase']
  config['challenge_module']='Palomar.Principal.BoltzmannDistances.Challenge'
  config['solution_module']='Palomar.Principal.BoltzmannDistances.Solution'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  check_challenge_config(spec,config)
 def test_named_proved_characterization_rejected_in_other_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.PlanarMap.mem_sourceSinkPathLengthsBase']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_actual_probability_theorem_allowed_only_for_cells(self):
  for module in ['CellLDP','CellSDP']:
   spec=copy.deepcopy(next(iter(load_challenges().values())))
   config=json.loads((ROOT/spec['config']).read_text())
   spec['path']='Palomar/Principal/'+module+'/Challenge.lean'
   spec['solution_path']='Palomar/Principal/'+module+'/Solution.lean'
   spec['declarations']=['DLQG1.Palomar.Principal.cell_ldp' if module=='CellLDP' else 'DLQG1.Palomar.Principal.cell_sdp']
   spec['proved_auxiliaries']=['DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure']
   config['challenge_module']='Palomar.Principal.'+module+'.Challenge'
   config['solution_module']='Palomar.Principal.'+module+'.Solution'
   config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
   check_challenge_config(spec,config)
 def test_actual_probability_theorem_rejected_for_unrelated_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
if __name__=='__main__':unittest.main()
