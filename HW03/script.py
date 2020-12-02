import re
import sys

def formatInput(file):
    a = []
    lines = file.readlines()
    for i in range(len(lines)):
        a.append(lines[i].split(","))
    for i in range(len(a)):
        for j in range(len(a[i])):
            if(a[i][j] == "w\n"):
                a[i][j] = "w";
            if(a[i][j] == ""):
                a[i][j] = "e";
    return a

def appendUnvisitedNeighbors(queue, coords, visited, inway, world):
    if ((world[coords[0] + 1][coords[1]] != "w") and ((coords[0] + 1, coords[1]) not in visited) and ((coords[0] + 1, coords[1]) not in queue) and ((coords[0] + 1, coords[1]) not in inway)):
        queue.append((coords[0] + 1, coords[1]))
    if ((world[coords[0] - 1][coords[1]] != "w") and ((coords[0] - 1, coords[1]) not in visited) and ((coords[0] - 1, coords[1]) not in queue) and ((coords[0] - 1, coords[1]) not in inway)):
        queue.append((coords[0] - 1, coords[1]))
    if ((world[coords[0]][coords[1] + 1] != "w") and ((coords[0], coords[1] + 1) not in visited) and ((coords[0], coords[1] + 1) not in queue) and ((coords[0], coords[1] + 1) not in inway)):
        queue.append((coords[0], coords[1] + 1))
    if ((world[coords[0]][coords[1] - 1] != "w") and ((coords[0], coords[1] - 1) not in visited) and ((coords[0], coords[1] - 1) not in queue) and ((coords[0], coords[1] - 1) not in inway)):
        queue.append((coords[0], coords[1] - 1))    

def walk(world, coords, out):
    queue = []
    inway = []
    inway.append(coords)

    visited = []


    dependants = []
    while (len(inway) != 0):
        inwayCoords = inway.pop(0)
        appendUnvisitedNeighbors(queue, inwayCoords, visited, inway, world)
        visited.append(inwayCoords)

        #
        
        dependants.append(world[inwayCoords[0]][inwayCoords[1]])
        while (len(queue) != 0):
            coords = queue.pop(0)

            if (world[coords[0]][coords[1]] == "w"):
                continue
            
            elif (world[coords[0]][coords[1]] != "e"):

                if out != None:
                    if len(dependants) == 0:
                        out.write("    next(" + world[coords[0]][coords[1]] + ") := " + world[coords[0]][coords[1]] + "\n")
                    elif len(dependants) >= 1:
                        out.write("    next(" + world[coords[0]][coords[1]] + ") :=\n" + "      case\n")
                        for dep in dependants:
                            if dep == dependants[0]:
                                out.write("        " + dep)
                            else:
                                out.write(" & " + dep)
                        if (re.findall("^d", world[coords[0]][coords[1]])):
                            out.write(" & " + "k" + world[coords[0]][coords[1]][1])
                        out.write(": TRUE;\n")
                        out.write("        TRUE : " + world[coords[0]][coords[1]] + ";\n" + "      esac;\n")
                    
                inway.append((coords[0], coords[1]))
                continue

            visited.append(coords)
            appendUnvisitedNeighbors(queue, coords, visited, inway, world)
   
    return dependants
    
def findMouse(world):
    for line in range(len(world)):
        for col in range(len(world[line])):
            if world[line][col] == "m":
                return (line, col)
    return None

def hasNearFree(pos, world):
    if (world[pos[0] + 1][pos[1]] == "e"): return True
    if (world[pos[0] - 1][pos[1]] == "e"): return True
    if (world[pos[0]][pos[1] + 1] == "e"): return True
    if (world[pos[0]][pos[1] - 1] == "e"): return True
    return False
def isNotInWalls(pos, world):
    if (world[pos[0] + 1][pos[1]] != "w"): return True
    if (world[pos[0] - 1][pos[1]] != "w"): return True
    if (world[pos[0]][pos[1] + 1] != "w"): return True
    if (world[pos[0]][pos[1] - 1] != "w"): return True
    return False
def createSMV(f):
    defaults = ["m", "c", "k1", "d1", "a", "p", "t"]

    
    
    world = formatInput(f)
    mousePos = findMouse(world)
    visited = walk(world, mousePos, None)

    defAndVisited = defaults
    for v in visited:
        if v not in defaults:
            defAndVisited.append(v)
    
    out = open("out.smv", "w")
    out.write("MODULE main\n")
    out.write("  VAR\n")
    for d in defAndVisited:
        out.write("    " + d + " : boolean;\n")              
    out.write("  ASSIGN\n")
    for d in defAndVisited:
        if d == "m":
            if not isNotInWalls(mousePos, world):
                out.write("    init(" + d + ") := FALSE;\n")
            elif not hasNearFree(mousePos, world):
                out.write("    init(" + d + ") := TRUE;\n")
        else:
            out.write("    init(" + d + ") := FALSE;\n")

    out.write("\n")
    out.write("    next(m) := m;\n")
    for d in defaults:
        if d not in visited:
            out.write("    next(" + d + ") := " + d + ";\n")
    
    walk(world, mousePos, out)
    
    out.close()
    
    

def main():
    if (len(sys.argv) != 2):
        print("Bad number of arguments")
        return
    f = open(sys.argv[1], "r")
    
    createSMV(f)
    f.close()
if __name__ == "__main__":
    main()

