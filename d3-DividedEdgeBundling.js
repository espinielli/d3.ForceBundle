/*
    Implementation of Divided Edge Bundling algorithm

    Reference:
        David Selassie, Brandon Heller, Jeffrey Heer
        "Divided Edge Bundling for Directional Network Data",
        IEEE Trans. Visualization & Comp. Graphics (Proc. InfoVis), 2011
        http://vis.stanford.edu/papers/divided-edge-bundling
    software: http://selassid.github.com/DividedEdgeBundling/
    paper: http://vis.stanford.edu/files/2011-DividedEdgeBundling-InfoVis.pdf

    Author: Enrico Spinielli, 2017
    (based on work from Corneliu S. (github.com/upphiminn) 2013)
 */

// conventions:
//   p, q    litteral nodes, i.e. {'x': ...,'y': ...}
//   e       litteral edge, i.e. {'source':'nodeid1', 'target':'nodeid2'}
//   P, Q    edge ids, i.e. "123"
!(function () {
  d3.DividedEdgeBundling = function () {
    var data_nodes = {}, // {'nodeid':{'x':,'y':},..}
      data_edges = [], // [{'source':'nodeid1', 'target':'nodeid2'},..]
      data_weights = [], // edges' weights
      compatibility_list_for_edge = [],
      subdivision_points_for_edge = [],
      K = 0.1, // global bundling constant controlling edge stiffness
      S_initial = 0.1, // init. distance to move points
      S_rate = 2, // init. distance to move points
      P_initial = 1, // init. subdivision number
      P_rate = 2, // subdivision rate increase
      C = 6, // number of cycles to perform
      I_initial = 90, // init. number of iterations for cycle
      I_rate = 0.6666667, // rate at which iteration number decreases i.e. 2/3
      compatibility_threshold = 0.6,
      eps = 1e-6

    /** Geometry Helper Methods **/
    function vector_dot_product (p, q) {
      return p.x * q.x + p.y * q.y
    }

    function normalize (v) {
      var len = Math.sqrt(v[0] * v[0] + v[1] * v[1])
      return [len * v[0], len * v[1]]
    }

    function edge_as_vector (P) {
      var sx = data_nodes[P.source].x
      var sy = data_nodes[P.source].y
      var tx = data_nodes[P.target].x
      var ty = data_nodes[P.target].y

      return {
        'x': tx - sx,
        'y': ty - sy
      }
    }

    function edge_length (e) {
      // handling nodes that are on the same location, so that K/edge_length != Inf
      if (Math.abs(data_nodes[e.source].x - data_nodes[e.target].x) < eps &&
                Math.abs(data_nodes[e.source].y - data_nodes[e.target].y) < eps) {
        return eps
      }

      return Math.sqrt(Math.pow(data_nodes[e.source].x - data_nodes[e.target].x, 2) +
                Math.pow(data_nodes[e.source].y - data_nodes[e.target].y, 2))
    }

    function custom_edge_length (e) {
      var sx = e.source.x
      var sy = e.source.y
      var tx = e.target.x
      var ty = e.target.y
      var dx = sx - tx
      var dy = sy - ty
      return Math.sqrt(dx * dx + dy * dy)
    }

    function edge_midpoint (e) {
      var sx = data_nodes[e.source].x
      var sy = data_nodes[e.source].y
      var tx = data_nodes[e.target].x
      var ty = data_nodes[e.target].y

      return {
        'x': (sx + tx) / 2.0,
        'y': (sy + ty) / 2.0
      }
    }

    function compute_divided_edge_length (e_idx) {
      var length = 0

      for (var i = 1; i < subdivision_points_for_edge[e_idx].length; i++) {
        var segment_length = euclidean_distance(subdivision_points_for_edge[e_idx][i], subdivision_points_for_edge[e_idx][i - 1])
        length += segment_length
      }

      return length
    }

    function euclidean_distance (p, q) {
      var dx = p.x - q.x
      var dy = p.y - q.y
      return Math.sqrt(dx * dx + dy * dy)
    }

    function project_point_on_line (p, Q) {
      // see "Minimum Distance between a Point and a Line"
      // by Paul Bourke
      // http://paulbourke.net/geometry/pointlineplane/
      var sx = Q.source.x
      var sy = Q.source.y
      var tx = Q.target.x
      var ty = Q.target.y
      var dx = tx - sx
      var dy = ty - sy

      var L = Math.sqrt(dx * dx + dy * dy)

      // if edges are coincidents return any of them
      if (L === 0.0) return {'x': sx, 'y': sy}
      var r = ((p.x - sx) * (tx - sx) + (p.y - sy) * (ty - sy)) / (L * L)

      return {
        'x': (sx + r * dx),
        'y': (sy + r * dy)
      }
    }

        /** * ********************** ***/

        /** * Initialization Methods ***/
    function initialize_edge_subdivisions () {
      for (var i = 0; i < data_edges.length; i++) {
        if (P_initial === 1) {
          subdivision_points_for_edge[i] = [] // 0 subdivisions
        } else {
          subdivision_points_for_edge[i] = []
          subdivision_points_for_edge[i].push(data_nodes[data_edges[i].source])
          subdivision_points_for_edge[i].push(data_nodes[data_edges[i].target])
        }
      }
    }

    function initialize_compatibility_lists () {
      for (var i = 0; i < data_edges.length; i++) {
        compatibility_list_for_edge[i] = [] // 0 compatible edges.
      }
    }

    function filter_self_loops (edgelist) {
      var filtered_edge_list = []

      for (var e = 0; e < edgelist.length; e++) {
        if (data_nodes[edgelist[e].source].x != data_nodes[edgelist[e].target].x ||
                    data_nodes[edgelist[e].source].y != data_nodes[edgelist[e].target].y) { // or smaller than eps
          filtered_edge_list.push(edgelist[e])
        }
      }

      return filtered_edge_list
    }

   /** *********************** ***/

   /** * Force Calculation Methods ***/
    function apply_spring_force (e_idx, i, kP) {
      var prev = subdivision_points_for_edge[e_idx][i - 1]
      var next = subdivision_points_for_edge[e_idx][i + 1]
      var crnt = subdivision_points_for_edge[e_idx][i]
      var scaling = 1000.0

      var w = data_weights[e_idx]
      var adj
      var tot = [0.0, 0.0]

      // previous edge
      adj = prev
      if (!adj) console.log('edgeidx = ' + e_idx + ', i = ' + i)
      var dx = adj.x - crnt.x
      var dy = adj.y - crnt.y
      var dist = Math.sqrt(dx * dx + dy * dy)
      var force = kP * dist * w / scaling

      var dir = normalize([dx, dy])
      var acc = [force * dir[0], force * dir[1]]
      tot = [tot[0] + acc[0], tot[1] + acc[1]]

      // next edge
      adj = next
      if (!adj) console.log('edgeidx = ' + e_idx + ', i = ' + i)
      dx = adj.x - crnt.x
      dy = adj.y - crnt.y
      dist = Math.sqrt(dx * dx + dy * dy)
      force = kP * dist * w / scaling

      dir = normalize([dx, dy])
      acc = acc = [force * dir[0], force * dir[1]]
      tot = [tot[0] + acc[0], tot[1] + acc[1]]

      return {
        'x': tot[0],
        'y': tot[1]
      }
    }

    function apply_electrostatic_force (e_idx, i) {
      var sum_of_forces = {
        'x': 0,
        'y': 0
      }
      var compatible_edges_list = compatibility_list_for_edge[e_idx]
      var force
      var idx

      // oe = other edge
      for (var oe = 0; oe < compatible_edges_list.length; oe++) {
        // var meshCount = subdivision_points_for_edge[compatible_edges_list[oe]].length

        //  //    float edgeDot = edgeDotsInCL[TriIndex(edgeIndex, otherEdgeIndex, edgeCount)];
        //  //    float otherEdgeWeight = edgeWeightsInCL[otherEdgeIndex];
        // var edge1 = data_edges[e_idx]
        // var edge2 = data_edges[compatible_edges_list[oe]]
        // var edgeDot = edge_as_vector(edge1, edge2)
        // var otherWeight = data_weights[compatible_edges_list[oe]]
        // var otherPointPos

        //  // If we're going the same direction as edge1, then use the points at the same index
        //  // and the potential minimum is at the point.
        // if (edgeDot >= 0.0) {
        //   idx = i
        //   otherPointPos = subdivision_points_for_edge[compatible_edges_list[oe]][idx]
        // }
        // // If we're going the opposite direction, use the complementary index and
        // // the potential minimum is edgeLaneWidth to the "right."
        //  // TODO: finish
        // else {
        //   idx = meshCount - i
        //  //       float2 tangent = normalize(edgeMeshesInCL[globalOtherPointIndex + 1] - edgeMeshesInCL[globalOtherPointIndex - 1]);
        //  //       float2 normal = (float2)(-tangent.y, tangent.x);
        //  //       otherPointPos = edgeMeshesInCL[globalOtherPointIndex] + normal * edgeLaneWidth;
        // }

         // dr = otherPointPos - pointPos;
         // dist = sqrt(dr.x * dr.x + dr.y * dr.y);

         // // If the point is on an edge that is being attracted directly to the other point and it's close enough,
         // // (depending on the size of the other bundle) say they're in the same group.
         //   float maxGroupRadius = pow(edgeWeight, bundleWidthPower) * edgeMaxWidth;

         // if (edgeDot >= 0.0f && (dist <= edgeMinWidth || dist <= maxGroupRadius))
         //    pointGroupWeight += otherEdgeWeight;

         //   // Inverse force.
         //   if (!useNewForce)
         //       force = edgeCoulombConstant * 30.0f / (meshCount - 1) / (dist + 0.01f);
         //   // New force.
         //   else
         //       force = 4.0f * 10000.0f / (meshCount - 1) * edgeCoulombDecay * edgeCoulombConstant * dist / (3.1415926f * pown(edgeCoulombDecay * edgeCoulombDecay + dist * dist, 2));
         // force *= otherEdgeWeight;

         // if (useCompat)
         //    force *= otherCompat;
        force = {
          'x': subdivision_points_for_edge[compatible_edges_list[oe]][i].x - subdivision_points_for_edge[e_idx][i].x,
          'y': subdivision_points_for_edge[compatible_edges_list[oe]][i].y - subdivision_points_for_edge[e_idx][i].y
        }

        if ((Math.abs(force.x) > eps) || (Math.abs(force.y) > eps)) {
          var diff = (1 / Math.pow(custom_edge_length({
            'source': subdivision_points_for_edge[compatible_edges_list[oe]][i],
            'target': subdivision_points_for_edge[e_idx][i]
          }), 1))

          sum_of_forces.x += force.x * diff
          sum_of_forces.y += force.y * diff
        }
      }

      return sum_of_forces
    }

    function apply_resulting_forces_on_subdivision_points (e_idx, P, S) {
      var kP = K / (edge_length(data_edges[e_idx]) * (P + 1)) // kP=K/|P|(number of segments), where |P| is the initial length of edge P.
            // (length * (num of sub division pts - 1))
      var resulting_forces_for_subdivision_points = [{
        'x': 0,
        'y': 0
      }]

      for (var i = 1; i < P + 1; i++) { // exclude initial end points of the edge 0 and P+1
        var resulting_force = {
          'x': 0,
          'y': 0
        }

        spring_force = apply_spring_force(e_idx, i, kP)
        electrostatic_force = apply_electrostatic_force(e_idx, i, S)

        resulting_force.x = S * (spring_force.x + electrostatic_force.x)
        resulting_force.y = S * (spring_force.y + electrostatic_force.y)

        resulting_forces_for_subdivision_points.push(resulting_force)
      }

      resulting_forces_for_subdivision_points.push({
        'x': 0,
        'y': 0
      })

      return resulting_forces_for_subdivision_points
    }

        /** * ********************** ***/

        /** * Edge Division Calculation Methods ***/
    function update_edge_divisions (P) {
      for (var e_idx = 0; e_idx < data_edges.length; e_idx++) {
        if (P === 1) {
          subdivision_points_for_edge[e_idx].push(data_nodes[data_edges[e_idx].source]) // source
          subdivision_points_for_edge[e_idx].push(edge_midpoint(data_edges[e_idx])) // mid point
          subdivision_points_for_edge[e_idx].push(data_nodes[data_edges[e_idx].target]) // target
        } else {
          var divided_edge_length = compute_divided_edge_length(e_idx)
          var segment_length = divided_edge_length / (P + 1)
          var current_segment_length = segment_length
          var new_subdivision_points = []
          new_subdivision_points.push(data_nodes[data_edges[e_idx].source]) // source

          for (var i = 1; i < subdivision_points_for_edge[e_idx].length; i++) {
            var old_segment_length = euclidean_distance(subdivision_points_for_edge[e_idx][i], subdivision_points_for_edge[e_idx][i - 1])

            while (old_segment_length > current_segment_length) {
              var percent_position = current_segment_length / old_segment_length
              var new_subdivision_point_x = subdivision_points_for_edge[e_idx][i - 1].x
              var new_subdivision_point_y = subdivision_points_for_edge[e_idx][i - 1].y

              new_subdivision_point_x += percent_position * (subdivision_points_for_edge[e_idx][i].x - subdivision_points_for_edge[e_idx][i - 1].x)
              new_subdivision_point_y += percent_position * (subdivision_points_for_edge[e_idx][i].y - subdivision_points_for_edge[e_idx][i - 1].y)
              new_subdivision_points.push({
                'x': new_subdivision_point_x,
                'y': new_subdivision_point_y
              })

              old_segment_length -= current_segment_length
              current_segment_length = segment_length
            }
            current_segment_length -= old_segment_length
          }
          new_subdivision_points.push(data_nodes[data_edges[e_idx].target]) // target
          subdivision_points_for_edge[e_idx] = new_subdivision_points
        }
      }
    }

        /** * ********************** ***/

        /** * Edge compatibility measures ***/
    function angle_compatibility (P, Q) {
      return Math.abs(vector_dot_product(edge_as_vector(P), edge_as_vector(Q)) / (edge_length(P) * edge_length(Q)))
    }

    function scale_compatibility (P, Q) {
      var lavg = (edge_length(P) + edge_length(Q)) / 2.0
      return 2.0 / (lavg / Math.min(edge_length(P), edge_length(Q)) + Math.max(edge_length(P), edge_length(Q)) / lavg)
    }

    function position_compatibility (P, Q) {
      var lavg = (edge_length(P) + edge_length(Q)) / 2.0
      var midP = {
        'x': (data_nodes[P.source].x + data_nodes[P.target].x) / 2.0,
        'y': (data_nodes[P.source].y + data_nodes[P.target].y) / 2.0
      }
      var midQ = {
        'x': (data_nodes[Q.source].x + data_nodes[Q.target].x) / 2.0,
        'y': (data_nodes[Q.source].y + data_nodes[Q.target].y) / 2.0
      }

      return lavg / (lavg + euclidean_distance(midP, midQ))
    }

    function edge_visibility (P, Q) {
      var I0 = project_point_on_line(data_nodes[Q.source], {
        'source': data_nodes[P.source],
        'target': data_nodes[P.target]
      })
      var I1 = project_point_on_line(data_nodes[Q.target], {
        'source': data_nodes[P.source],
        'target': data_nodes[P.target]
      }) // send actual edge points positions
      var midI = {
        'x': (I0.x + I1.x) / 2.0,
        'y': (I0.y + I1.y) / 2.0
      }
      var midP = {
        'x': (data_nodes[P.source].x + data_nodes[P.target].x) / 2.0,
        'y': (data_nodes[P.source].y + data_nodes[P.target].y) / 2.0
      }

      return Math.max(0, 1 - 2 * euclidean_distance(midP, midI) / euclidean_distance(I0, I1))
    }

    function visibility_compatibility (P, Q) {
      return Math.min(edge_visibility(P, Q), edge_visibility(Q, P))
    }

    function compatibility_score (P, Q) {
      return (angle_compatibility(P, Q) * scale_compatibility(P, Q) * position_compatibility(P, Q) * visibility_compatibility(P, Q))
    }

    function are_compatible (P, Q) {
      return (compatibility_score(P, Q) >= compatibility_threshold)
    }

    function compute_compatibility_lists () {
      for (var e = 0; e < data_edges.length - 1; e++) {
        for (var oe = e + 1; oe < data_edges.length; oe++) { // don't want any duplicates
          if (are_compatible(data_edges[e], data_edges[oe])) {
            compatibility_list_for_edge[e].push(oe)
            compatibility_list_for_edge[oe].push(e)
          }
        }
      }
    }

        /** * ************************ ***/

        /** * Main Bundling Loop Methods ***/
    var forcebundle = function () {
      var S = S_initial
      var I = I_initial
      var P = P_initial

      initialize_edge_subdivisions()
      initialize_compatibility_lists()
      update_edge_divisions(P)
      compute_compatibility_lists()

      for (var cycle = 0; cycle < C; cycle++) {
        for (var iteration = 0; iteration < I; iteration++) {
          var forces = []
          for (var edge = 0; edge < data_edges.length; edge++) {
            forces[edge] = apply_resulting_forces_on_subdivision_points(edge, P, S)
          }
          for (var e = 0; e < data_edges.length; e++) {
            for (var i = 0; i < P + 1; i++) {
              subdivision_points_for_edge[e][i].x += forces[e][i].x
              subdivision_points_for_edge[e][i].y += forces[e][i].y
            }
          }
        }
                // prepare for next cycle
        S = S / S_rate
        P = P * P_rate
        I = I_rate * I

        update_edge_divisions(P)
                // console.log('C' + cycle);
                // console.log('P' + P);
                // console.log('S' + S);
      }
      return subdivision_points_for_edge
    }
        /** * ************************ ***/

        /** * Getters/Setters Methods ***/
    forcebundle.nodes = function (nodes) {
      if (arguments.length === 0) {
        return data_nodes
      } else {
        data_nodes = nodes
      }

      return forcebundle
    }

    forcebundle.edges = function (edges) {
      if (arguments.length === 0) {
        return data_edges
      } else {
        data_edges = filter_self_loops(edges) // remove edges to from to the same point
      }

      return forcebundle
    }

    forcebundle.weights = function (weights) {
      if (arguments.length === 0) {
        return data_weights
      } else {
        data_weights = weights
      }

      return forcebundle
    }

    forcebundle.bundling_stiffness = function (k) {
      if (arguments.length === 0) {
        return K
      } else {
        K = k
      }

      return forcebundle
    }
    forcebundle.K = forcebundle.bundling_stiffness

    forcebundle.cycles = function (c) {
      if (arguments.length === 0) {
        return C
      } else {
        C = c
      }

      return forcebundle
    }
    forcebundle.C = forcebundle.cycles

    //  ************  STEPS (S0, S) ************
    forcebundle.step_size = function (step) {
      if (arguments.length === 0) {
        return S_initial
      } else {
        S_initial = step
      }

      return forcebundle
    }
    forcebundle.S0 = forcebundle.step_size

    forcebundle.step_rate = function (step) {
      if (arguments.length === 0) {
        return S_rate
      } else {
        S_rate = step
      }

      return forcebundle
    }
    forcebundle.S = forcebundle.step_rate

    //  ************  ITERATIONS (I0, I) ************
    forcebundle.iterations = function (i) {
      if (arguments.length === 0) {
        return I_initial
      } else {
        I_initial = i
      }

      return forcebundle
    }
    forcebundle.I0 = forcebundle.iterations

    forcebundle.iterations_rate = function (i) {
      if (arguments.length === 0) {
        return I_rate
      } else {
        I_rate = i
      }

      return forcebundle
    }
    forcebundle.I = forcebundle.iterations_rate

    //  ************  SUBDIVISIONS (P0, P) ************
    forcebundle.subdivision_points_seed = function (p) {
      if (arguments.length == 0) {
        return P
      } else {
        P = p
      }

      return forcebundle
    }
    forcebundle.P0 = forcebundle.subdivision_points_seed

    forcebundle.subdivision_rate = function (r) {
      if (arguments.length === 0) {
        return P_rate
      } else {
        P_rate = r
      }

      return forcebundle
    }
    forcebundle.P = forcebundle.subdivision_rate

    //  ************  COMPATIBILITY THRESHOLD ************
    forcebundle.compatibility_threshold = function (t) {
      if (arguments.length === 0) {
        return compatibility_threshold
      } else {
        compatibility_threshold = t
      }

      return forcebundle
    }
    forcebundle.Ct = forcebundle.compatibility_threshold
        /** * ************************ ***/

    return forcebundle
  }
})()
