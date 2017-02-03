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

// nodes is an array of objects
// nodes = [
//   {'id': 'EBBR', 'x': 1.23, 'y': 3.45, ...}
//   {'id': 'LFPG', 'x': 1.56, 'y': 7.89, ...}
//   ...
// ]
//
// edges = [
//   {'s': '0', 't': '1', 'weight': 1.2} // from EBBR to LFPG
//   {'s': '5', 't': '7', 'weight': 0.5}
//   {'s': '0', 't': '1', 'weight': 9.1}
// ]

// node {'id':..., 'attrs':{}}
//     attrs can be something like {'x':..., 'y':..., 'name':...}
// edge {'v':..., 'w':..., 'attrs':{}}
//     attrs can be something like {'weight':..., 'name':...}

!(function () {
  d3.DividedEdgeBundling = function () {
    var K = 0.1     // edge stiffness
    var C = 6       // number of cycles to perform
    var S0 = 0.04   // initial step size
    var S = 2       // step subdivision rate
    var I0 = 50     // initial number of iterations per cycle
    var I = 3.0 / 2 // number of iterations subdivision rate
    var P0 = 1      // initial number of subdivision points (>=1)
    var P = 2       // number of subdivision points subdivision rate
    var Ct = 0.05   // compatibility threshold
    var distanceFunction = euclideanDistance // calculate the distance between two points
    var pointAtDistanceFunction = euclideanPointAtDistance // return a point at distance,d, along the segment
    var pointAlongSegment = euclideanPointAtDistance

    var earthR = 6371000 // Earth mean radius in meters
    var radians = 180 / Math.PI
    var degrees = Math.PI / 180
    var sin = Math.sin
    var cos = Math.cos
    var asin = Math.asin
    var acos = Math.acos
    var atan2 = Math.atan2
    var sqrt = Math.sqrt

    var edges = []
    var nodes = []
    var meshes = [] // all subdivision points for an edge, an array of [x, y] coordinates

    function euclideanDistance (p0, p1) {
      var dx = p1[0] - p0[0]
      var dy = p1[1] - p0[1]

      return sqrt(dx * dx + dy * dy)
    }

    // return the point at distance, d, along the segment from p0 to p1
    function euclideanPointAtDistance (p0, p1, d) {
      var L = euclideanDistance(p0, p1)
      var dx = p1[0] - p0[0]
      var dy = p1[1] - p0[1]
      var pct = d / L
      var xd = p0[0] + pct * dx
      var yd = p0[1] + pct * dy

      return [xd, yd]
    }

    // return the point at distance, d, along the great circle segment from p0 to p1
    // we assume first coordinat as longitude in degrees, second is latitude
    // d in meters
    function geoPointAtDistance (p0, p1, d) {
      // see http://www.movable-type.co.uk/scripts/latlong.html
      var p0rad = [p0[0] * radians, p0[1] * radians]
      var p1rad = [p1[0] * radians, p1[1] * radians]
      var dLon = p1rad[1] - p0rad[1] // delta in longitudes
      // θ = atan2( sin Δλ ⋅ cos φ1 , cos φ0 ⋅ sin φ1 − sin φ0 ⋅ cos φ1 ⋅ cos Δλ )
      var bearing = atan2(sin(dLon) * cos(p1rad[0]),
        cos(p0rad[0]) * sin(p1rad[0]) - sin(p0rad[0]) * cos(p1rad[0]) * cos(dLon))
      var delta = d / earthR

      // φ2 = asin( sin φ0 ⋅ cos δ + cos φ0 ⋅ sin δ ⋅ cos θ )
      // λ2 = λ0 + atan2( sin θ ⋅ sin δ ⋅ cos φ0, cos δ − sin φ0 ⋅ sin φ1 )
      // φ is latitude, λ is longitude, θ is the bearing (clockwise from north),
      // δ is the angular distance d/R; d being the distance travelled, R the earth’s radius
      var p2rad = []
      p2rad[0] = asin(sin(p0rad[0]) * cos(delta) + cos(p0rad[0]) * sin(delta) * cos(bearing))
      p2rad[1] = p0rad[1] + atan2(sin(bearing) * sin(delta) * cos(p0rad[0]), cos(delta) - sin(p0rad[0]) * sin(p1rad[0]))

      // normalize and convert to degrees
      p2rad[0] = (p2rad[0] + 540) % 360 - 180
      return [p2rad[0] * degrees, p2rad[1] * degrees]
    }

    // return a new mesh split at 'meshLength' distance along the old segments
    function mesh (meshPoints, newLength) {
      var curr = meshPoints[0]
      var next
      var newMesh = []
      newMesh.push(curr)
      var remainingSegmentLen = 0

      for (var i = 1; i < meshPoints.length; i++) {
        next = meshPoints[i]
        remainingSegmentLen += distanceFunction(curr, next)
        while (remainingSegmentLen >= newLength) {
          newPoint = pointAlongSegment(curr, next, newLength)
          newMesh.push(newPoint)
          remainingSegmentLen -= newLength
          curr = newPoint
        }
        remainingSegmentLen = -remainingSegmentLen
        curr = next
      }

      // push target if it is not last entry
      if (remainingSegmentLen != 0.0) {
        newMesh.push(meshPoints[meshPoints.length - 1])
      }

      return newMesh
    }

    // calculate the total mesh length
    // meshPoints is a vector of coordinates
    function meshLength (meshPoints) {
      var curr = meshPoints[0]
      var next
      var totalLen = 0.0
      for (var i = 1; i < meshPoints.length; i++) {
        next = meshPoints[i]
        totalLen += distanceFunction(curr, next)
        curr = next
      }

      return totalLen
    }

    function updateEdgeSubdivision (p) {
      // take meshes and dived the whole set in 'p' parts
      // 'p' is Pi * P, initially 'p' is P0
      //  where Pi is the number of subdivision points at cycly 'i'
      //  and P is the rate of subdivision for subdivision points
      var e
      var ml
      for (var i = 0; i < meshes.length; i++) {
        e = meshes[i]
        ml = meshLength(meshes[i])
        meshes[i] = mesh(e, ml / p)
      }
    }

    // update edge compatibility list
    function updateEdgeCompatibilityList () {
    }

    // update position of mesh points according to acting forces
    function updateMeshPoints () {

    }

    //
    function initializeMeshes () {
      for (var i = 0; i < edges.length; i++) {
        var e = edges[i]
        var s = nodes[e.source]
        var t = nodes[e.target]
        var sourceCoords = [s.x, s.y]
        var targetCoords = [t.x, t.y]
        meshes[i] = [sourceCoords, targetCoords]
      }
    }

    // ****************
    // main calculation
    // ****************
    var deb = function () {
      var iterations = I0
      var p = P0

      for (var c = 0; c < C; c++) {
        p *= P
        for (var i = 0; i < iterations; i++) {
          updateEdgeSubdivision(p)
          updateEdgeCompatibilityList()
          updateMeshPoints()
        }
        // prepare for next cycle
      }

      return bundles
    }

    deb.updateEdgeSubdivision = updateEdgeSubdivision
    deb.meshLength = meshLength
    deb.mesh = mesh

    deb.nodes = function (ns) {
      if (arguments.length === 0) {
        return nodes
      } else {
        nodes = ns
      }

      return deb
    }

    deb.edges = function (es) {
      if (arguments.length === 0) {
        return edges
      } else {
        edges = es
      }
      initializeMeshes()
      return deb
    }

    deb.meshes = function () {
      return meshes
    }

    deb.K = function (k) {
      if (arguments.length === 0) {
        return K
      } else {
        K = k
      }

      return deb
    }

    // number of cycles to perform
    deb.C = function (c) {
      if (arguments.length === 0) {
        return C
      } else {
        C = c
      }

      return deb
    }

    // initial distance to move points
    deb.S0 = function (s0) {
      if (arguments.length === 0) {
        return S0
      } else {
        S0 = s0
      }

      return deb
    }

    // step subdivision rate
    deb.S = function (s) {
      if (arguments.length === 0) {
        return S
      } else {
        S = s
      }

      return deb
    }

    // initial number of iterations per cycle
    deb.I0 = function (i0) {
      if (arguments.length === 0) {
        return I0
      } else {
        I0 = i0
      }

      return deb
    }

    // iteration subdivision rate
    deb.I = function (i) {
      if (arguments.length === 0) {
        return I
      } else {
        I = i
      }

      return deb
    }

    // initial number of subdivision points (>=1)
    deb.P0 = function (p0) {
      if (arguments.length === 0) {
        return P0
      } else {
        P0 = p0
      }

      return deb
    }

    // number of subdivision points subdivision rate
    deb.P = function (p) {
      if (arguments.length === 0) {
        return P
      } else {
        P = p
      }

      return deb
    }

    // compatibility threshold
    deb.Ct = function (t) {
      if (arguments.length === 0) {
        return Ct
      } else {
        Ct = t
      }

      return deb
    }

    return deb
  }
})()
