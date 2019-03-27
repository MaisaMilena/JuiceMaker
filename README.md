# JuiceMaker

## Using Agda - for programmers

You have a Juice Maker, which has Ingredients (orange, pineapple, beet, etc) and Items, which are composed by a quantity of ingredient (mesured in ml) and an item.

It is required to restrict the combination of items. In this case, they can only be 100ml of orange or 50ml of beet. So, a combination of 150ml orange is not valid and should not be accepted by Agda. 

To make a juice, you use a series of events like pick an item and add it to the list of items to make a juice, undo the last action, copy the last action and finish the ordering of juice.

In the end, the list of items will be validated to check if it has 300ml or not. Whithout having this amount, is not possible to make a juice. 

This exercice uses [Human library](https://github.com/MaiaVictor/agda-for-humans), no standart library is used. 

### Work with
- Pair
- Subset (sigma)
- Defining data types
- List 
- Map 
- Lambda
- With clause
- Pattern matching
- Equality 
- Maybe 

### TODO
- Can or cannot make the juice:   
   [ ] check if it has 300ml  
   [ ] check if it has the maxium of 3 types of ingredients

