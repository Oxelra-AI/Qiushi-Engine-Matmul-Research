#!/usr/bin/env python3
"""analysis: verify cut tautology in non-zero branches and analyze relation row activity.

The review observes that all 96 transported support cuts contain at least one
point from orbit O={1,3,9}, so they are tautological in every branch that forbids O.
Relation rows involve more quotient points and may remain nontrivial.
"""
import json, hashlib
from pathlib import Path

ROOT = Path('research/research_record/workspace')
BRANCH_SPECS = ROOT / 'data/quotient_branches/corrected_branch_specs.json'
TRANSPORT1 = ROOT / 'data/quotient_lift/transport/rank2_lift_cut_stabilizer_transport.json'
TRANSPORT2 = ROOT / 'data/quotient_lift/transport/rank2_survivor2_lift_cut_stabilizer_transport.json'
RELATIONS = ROOT / 'data/quotient_lift/transport/rank2_lift_relation_rows_from_cut33.json'
OUT = ROOT / 'data/quotient_lift/cut_tautology_relation_activity.json'

def main():
    specs = json.loads(BRANCH_SPECS.read_text())
    rank2_branches = specs['pivots']['rank2']['branches']
    
    # Load transported cuts
    t1 = json.loads(TRANSPORT1.read_text())
    t2 = json.loads(TRANSPORT2.read_text())
    
    cuts_orbit1 = [set(c['cut_points']) for c in t1['unique_cuts']]
    cuts_orbit2 = [set(c['cut_points']) for c in t2['unique_cuts']]
    all_cuts = cuts_orbit1 + cuts_orbit2
    
    O = {1, 3, 9}  # orbit 0
    
    # Verify: every transported cut contains at least one O-point
    orbit1_O_sizes = [len(c & O) for c in cuts_orbit1]
    orbit2_O_sizes = [len(c & O) for c in cuts_orbit2]
    
    cut_tautology_analysis = {
        'orbit_0_points': sorted(O),
        'orbit1_O_intersection_counts': dict(sorted(
            {str(k): orbit1_O_sizes.count(k) for k in set(orbit1_O_sizes)}.items())),
        'orbit2_O_intersection_counts': dict(sorted(
            {str(k): orbit2_O_sizes.count(k) for k in set(orbit2_O_sizes)}.items())),
        'all_cuts_contain_O_point': all(len(c & O) >= 1 for c in all_cuts),
        'min_O_intersection_orbit1': min(orbit1_O_sizes),
        'min_O_intersection_orbit2': min(orbit2_O_sizes),
    }
    
    # For each open branch, check cut tautology
    branch_cut_analysis = []
    open_branches = [0, 1, 2, 5]
    for br_spec in rank2_branches:
        b = br_spec['branch']
        if b not in open_branches:
            continue
        forbidden = set(br_spec['forbid'])
        force = set(br_spec['force'])
        
        # A cut Σ_{p∈A} x_p ≤ 11 is tautological if |A \ forbidden| ≤ 11
        n_tautological = sum(1 for c in all_cuts if len(c - forbidden) <= 11)
        n_active = sum(1 for c in all_cuts if len(c - forbidden) > 11)
        
        # More detailed: max selectable from any cut
        max_selectable = max(len(c - forbidden) for c in all_cuts) if all_cuts else 0
        
        branch_cut_analysis.append({
            'branch': b,
            'forbidden_count': len(forbidden),
            'forbidden_includes_O': O.issubset(forbidden),
            'total_cuts': len(all_cuts),
            'tautological_cuts': n_tautological,
            'active_cuts': n_active,
            'max_selectable_from_any_cut': max_selectable,
        })
    
    # Load relation rows
    rel_data = json.loads(RELATIONS.read_text())
    relations = rel_data['relation_rows']
    
    # Analyze relation row activity in each open branch
    branch_relation_analysis = []
    for br_spec in rank2_branches:
        b = br_spec['branch']
        if b not in open_branches:
            continue
        forbidden = set(br_spec['forbid'])
        force = set(br_spec['force'])
        domain = set(range(1, 256)) - forbidden
        
        n_nontrivial = 0
        n_tautological = 0
        nontrivial_by_cap = {}
        nontrivial_by_dim = {}
        nontrivial_examples = []
        
        for rel in relations:
            eps0_pts = set(rel['eps0_points'])
            eps1_pts = set(rel['eps1_points'])
            cap = rel['cap']
            dim = rel['source_dim']
            
            # Active points are those in domain
            active_eps0 = eps0_pts & domain
            active_eps1 = eps1_pts & domain
            
            # The constraint is: sum_{p in active_eps0} y0_p + sum_{p in active_eps1} y1_p <= cap
            # For a selected point p: y0_p + y1_p = x_p = 1
            # If p in active_eps0 ∩ active_eps1: contributes 1 regardless of lift
            # If p in active_eps0 only: contributes y0_p (0 or 1)
            # If p in active_eps1 only: contributes y1_p (0 or 1)
            
            both = active_eps0 & active_eps1
            only0 = active_eps0 - active_eps1
            only1 = active_eps1 - active_eps0
            
            # Maximum possible contribution = |both| + |only0| + |only1| (all lift choices bad)
            # But with target 19, the LHS depends on how many points we select
            # The constraint is nontrivial if it can reject at least one 19-support in domain
            
            # Conservative: nontrivial if max_lhs_from_domain > cap where max_lhs = |both ∪ only0 ∪ only1|
            # But this is too conservative. Better: nontrivial if selecting 19 from domain
            # could violate the constraint.
            # Minimum LHS contribution = |both| (if all only0/only1 points are not selected)
            # This is only a lower bound on the minimum.
            
            # Actually, for support selection: the relation constrains lift choices.
            # If we select k points from both + k0 from only0 + k1 from only1, 
            # LHS = k + k0*y0 + k1*y1 where y0,y1 ∈ {0,1}
            # The constraint is nontrivial if k > cap or if k + k0 > cap or k + k1 > cap
            # (because we could have all y0=1 or all y1=1)
            
            # Most importantly: it constrains lift choices when k + max(k0,k1) > cap
            
            total_active = len(both | only0 | only1)
            
            # Is it nontrivial for 19-supports in domain?
            # If |domain| <= 19, everyone is selected, and max_lhs = total_active
            # If total_active <= cap, always satisfied → tautological
            if total_active <= cap:
                n_tautological += 1
                continue
            
            n_nontrivial += 1
            cap_key = str(cap)
            dim_key = str(dim)
            nontrivial_by_cap[cap_key] = nontrivial_by_cap.get(cap_key, 0) + 1
            nontrivial_by_dim[dim_key] = nontrivial_by_dim.get(dim_key, 0) + 1
            
            if len(nontrivial_examples) < 5:
                nontrivial_examples.append({
                    'cap': cap, 'dim': dim,
                    'active_both': len(both),
                    'active_only0': len(only0),
                    'active_only1': len(only1),
                    'total_active': total_active,
                    'points_removed_by_forbid': len((eps0_pts | eps1_pts) - domain),
                })
        
        branch_relation_analysis.append({
            'branch': b,
            'forbidden_count': len(forbidden),
            'domain_size': len(domain),
            'total_relation_rows': len(relations),
            'nontrivial_relation_rows': n_nontrivial,
            'tautological_relation_rows': n_tautological,
            'nontrivial_by_cap': dict(sorted(nontrivial_by_cap.items())),
            'nontrivial_by_dim': dict(sorted(nontrivial_by_dim.items())),
            'nontrivial_examples': nontrivial_examples,
        })
    
    out = {
        'cut_tautology_analysis': cut_tautology_analysis,
        'branch_cut_analysis': branch_cut_analysis,
        'branch_relation_analysis': branch_relation_analysis,
        'schema': 's0908_cut_tautology_relation_activity_v1',
    }
    
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True))
    print('saved', OUT)

if __name__ == '__main__':
    main()
