function reload()
  dofile("day1.lua")
end

function print_table(t)
  for k,v in ipairs(t) do
    print(k .. ": " .. v)
  end
end

-- Write a function called concatenate(a1, a2) that takes two arrays and returns a new array with all the elements of a1 followed by all the elements of a2.

function concatenate(a1, a2)
  local result = {}
  for _,v in ipairs(a1) do
    result[#result+1] = v
  end
  for _,v in ipairs(a2) do
    result[#result+1] = v
  end
  return result
end

-- Change the global metatable you discovered in the Find section earlier so that any time you try to add two arrays using the plus sign (e.g., a1 + a2), Lua concatenates them together using your concatenate() function.

gmt = getmetatable(_G) or {}
gmt.__add = concatenate
setmetatable(_G, gmt)


